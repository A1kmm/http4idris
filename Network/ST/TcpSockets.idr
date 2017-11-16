module Network.ST.TcpSockets

import Control.ST

import Network.Socket

public export data TcpSocketState = Ready | Bound | Listening | Connected | Failed

export addressIPv4 : Int -> Int -> Int -> Int -> SocketAddress
addressIPv4 a b c d = IPv4Addr a b c d

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
  listen : (sock : Var) -> ST m Bool [sock ::: Sock Bound :-> (\v => if v then Sock Bound else Sock Failed)]
  accept : (listeningSocket : Var)
           -> (withNewSocket : (newAddr: SocketAddress) -> (newSocket : Var)
                -> ST m () [remove newSocket (Sock Connected)])
           -> ST m (Maybe SocketAddress) [
                listeningSocket ::: Sock Listening
              ]
  close : {origSt : TcpSocketState} -> (sock : Var) -> ST m () [remove sock (Sock origSt)]

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
    delete sockVar
  )
  where
  forkIO : IO () -> IO ()
  forkIO f = do
    fork f
    pure ()
  forkST : ST IO () [] -> ST IO () []
  forkST = ST.lift . forkIO . ST.run
