module Network.Wai
import Control.ST
import Network.ST.TcpSockets
import Network.Socket.Data

data PendingRequest = MkPendingRequest

data Request = MkRequest
data Response = MkResponse

interface CanRespondHTTP (m : Type -> Type) where
  respondHttp : Response -> ST m () [remove pendingRequest PendingRequest]

data Application : (m : Type -> Type) -> Type where
  MkApplication : ((pendingRequest : Var) -> (Response -> ST m () [remove pendingRequest PendingRequest]) 
                   -> (req : Request) -> ST m () [remove pendingRequest PendingRequest])
                   -> Application m

runApplication : (m : Type -> Type)
                 -> {tcpSockets: TcpSockets m}
                 -> (bindTo: Maybe SocketAddress)
                 -> (port: Int)
                 -> (app: Application m)
                 -> ST m String []
runApplication m {tcpSockets} bindTo port app =
  do
    Just listenerSocket <- socket tcpSockets
      | Nothing => pure "Can't create listener socket"
    True <- bind tcpSockets bindTo port listenerSocket
      | False => do
         close tcpSockets listenerSocket
         pure "Can't bind listener to port"
    True <- listen tcpSockets listenerSocket
      | False => do
         close tcpSockets listenerSocket
         pure "Can't listen on listener socket"
    err <- applicationAcceptLoop listenerSocket
    close tcpSockets listenerSocket
    pure err  
  where
    incomingConnectionLoop : (sourceAddr : SocketAddress)
                          -> (sock : Var)
                          -> ST m () [remove sock (Sock tcpSockets Connected)]
    incomingConnectionLoop = ?fixMe
      -- TODO: Consider some kind of timeout on incoming connections
      
    applicationAcceptLoop : (listener: Var) -> ST m String [listener ::: Sock tcpSockets Listening :-> Sock tcpSockets Failed]
    applicationAcceptLoop listener = do
      -- TODO: Consider some kind of limit on the number of open connections to
      -- avoid a DoS
      Just _ <- accept tcpSockets listener incomingConnectionLoop
        | Nothing => pure "Failed to accept"
      applicationAcceptLoop listener
