module Network.ST.TcpSockets

import Control.ST
import Network.Socket

data TcpSocketState = Ready | Bound | Listening | Connected | Closed

export addressIPv4 : Int -> Int -> Int -> Int -> SocketAddress
addressIPv4 a b c d = IPv4Addr a b c d

-- Interface built using record not interface so we can use Sock more
-- easily.
record TcpSockets (m : Type -> Type) where
  constructor MkTcpSockets
  Sock : TcpSocketState -> Type
  socket : ST m (Maybe Var) [addIfJust $ Sock Ready]
  bind : (bindAddr: Maybe SocketAddress)
         -> (port : Int)
         -> (sock : Var)
         -> ST m Bool [sock ::: Sock Ready :-> (\v => if v then Sock Bound else Sock Closed)]

MyType : TcpSocketState -> Type
MyType st = State ()

varInSomeState : (var: Var) -> ST m () [var ::: MyType Ready :-> MyType Bound]
varInSomeState v = with ST pure ()

otherVarInSomeState : (var: Var) -> ST m () [var ::: MyType Ready]
otherVarInSomeState v = varInSomeState v

%hint ioTcpSockets : TcpSockets IO
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

myWeirdBind : {auto socketConstraint : TcpSockets m} -> (bindAddr: Maybe SocketAddress) -> (port : Int) -> (sock : Var) -> ST m Bool [ sock ::: (Sock socketConstraint Ready :-> (\v => if v then Sock socketConstraint Bound else Sock socketConstraint Closed)) ]
myWeirdBind {socketConstraint} a p s = bind socketConstraint a p s
