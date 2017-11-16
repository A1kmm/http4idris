module Network.ST.TcpSockets

import Control.ST

import Network.Socket

public export data TcpSocketState = Ready | Bound | Listening | Connected | Failed

public export addFirstIfJust : Type -> Action (Maybe (Var, a))
addFirstIfJust ty = Add (
  \inp => case inp of
    Nothing => []
    Just (v, _) => [v ::: ty ]
                        )

-- Interface built using record not interface so we can use Sock more
-- easily.
public export record TcpSockets (m : Type -> Type) where
  constructor MkTcpSockets
  Sock : TcpSocketState -> Type
  socket : ST m (Maybe Var) [addIfJust $ Sock Ready]
  bind : (bindAddr: Maybe SocketAddress)
         -> (port : Int)
         -> (sock : Var)
         -> ST m Bool [sock ::: Sock Ready :-> (\v => if v then Sock Bound else Sock Ready)]
  listen : (sock : Var) -> ST m Bool [sock ::: Sock Bound :-> (\v => if v then Sock Listening else Sock Failed)]
  accept : (listeningSocket : Var)
           -> (withNewSocket : (newAddr: SocketAddress) -> (newSocket : Var)
                -> ST m () [remove newSocket (Sock Connected)])
           -> ST m (Maybe SocketAddress) [
                listeningSocket ::: Sock Listening :-> maybe (Sock Failed) (const $ Sock Listening)
              ]
  close : {origSt : TcpSocketState} -> (sock : Var) -> ST m () [remove sock (Sock origSt)]
  readSocket : (sock : Var) -> ST m (Maybe String) [
    sock ::: Sock Connected :-> maybe (Sock Failed) (\_ => Sock Connected)
  ]
  writeSocket : (out : String) -> (sock : Var) -> ST m (Maybe String) [
    sock ::: Sock Connected :-> maybe (Sock Failed) (const $ Sock Connected)
  ]

-- Hardcoded for now - if not, we need to prove it is within bound and non-negative
readBufSize : ByteLength
readBufSize = 4096

%hint export ioTcpSockets : TcpSockets IO
ioTcpSockets = MkTcpSockets
  {- Sock -} (const $ State Socket)
  {- socket -} (do
    Right rawSocket <- lift $ Socket.socket AF_INET6 Stream 0
      | Left _ => pure Nothing
    lbl <- new rawSocket
    pure (Just lbl))
  {- bind -} (\addr => \port => \sockVar => do
    resultCode <- (lift $ Socket.bind !(read sockVar) addr port)
    if resultCode == 0 then
      pure True
    else
      pure False)
  {- listen -} (\sockVar => do
    resultCode <- lift $ Socket.listen !(read sockVar)
    if resultCode == 0 then
      pure True
    else
      pure False)
  {- accept -} (\listeningSockVar => \withNewSocket => with ST do
    Right (newSock, addr) <- lift $ Socket.accept !(read listeningSockVar)
     | Left _ => pure Nothing
    call $ forkST $ with ST do
      newSockVar <- new newSock
      withNewSocket addr newSockVar
    pure $ Just addr)
  {- close -} (\sockVar => do
    lift $ Socket.close !(read sockVar)
    delete sockVar)
  {- readSocket -} (\sockVar => with ST do
      Right (resp, _) <- lift $ Socket.recv !(read sockVar) readBufSize
       | Left _ => pure Nothing
      pure (Just resp))
  {- writeSocket -} (\out => \sockVar => with ST do
      Right count <- lift $ Socket.send !(read sockVar) out
       | Left _ => pure Nothing
      let countNat : Nat = cast count
      
      -- Here we assert that any successful (non-negative) return value from
      -- send is less than or equal to the original size of the buffer. The manpage
      -- for send says:
      --   On success, these calls return the number of bytes sent.
      --   On error, -1 is returned, and errno is set appropriately.
      -- For this assertion to be falsified, the kernel would need to be telling us
      -- it had sent more data than we asked it to, which is against the contract
      -- of send.
      let sendReturnValueLTELength : LTE countNat (length out) = believe_me ()
      pure $ Just $ substr countNat ((length out) - countNat) out
    )
  where
  forkIO : IO () -> IO ()
  forkIO f = do
    fork f
    pure ()
  forkST : ST IO () [] -> ST IO () []
  forkST = ST.lift . forkIO . ST.run
