module Network.Wai
import Control.ST
import Network.ST.TcpSockets
import Network.ST.IOUtils
import Network.Socket.Data

public export
data PendingRequest = MkPendingRequest

public export
record HttpResponseCode where
  constructor MkHttpResponseCode
  responseNumber : Nat  -- TODO: Static guarantee it is in range?
  responseText : String -- TODO: Static guarantee String has no whitespace?

public export
record HttpHeader where
  constructor MkHttpHeader
  headerName: String -- TODO: Static guarantee it doesn't have whitespace?
  headerValue: String -- TODO: Static guarantee it doesn't have newline?

public export
record HttpRequest where
  constructor MkHttpRequest
  method : String
  headers : List HttpHeader
  body : String

public export
record HttpResponse where
  constructor MkHttpResponse
  code : HttpResponseCode
  headers : List HttpHeader

public export
data InvalidRequestOr : a -> Type where
  ValidRequest : a -> InvalidRequestOr a
  InvalidRequest : InvalidRequestOr a

public export
interface CanRespondHTTP (m : Type -> Type) where
  respondHttp : HttpResponse -> ST m () [remove pendingRequest PendingRequest]

public export
data Application : (m : Type -> Type) -> Type where
  MkApplication : ((pendingRequest : Var) -> (HttpResponse -> ST m () [remove pendingRequest PendingRequest]) 
                   -> (req : HttpRequest) -> ST m () [remove pendingRequest PendingRequest])
                   -> Application m

export
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
    readHTTPHeaders : (sock : BufferedSocket) ->
                      ST m (Maybe (InvalidRequestOr HttpRequest)) (maybeBufferedSocketFails {tcpSocketInstance = tcpSockets} {ty = (InvalidRequestOr HttpRequest)} sock)
    readHTTPHeaders sock = with ST do
      Just result <- readLineFromSocket sock
        | Nothing => pure Nothing
      let (method, afterMethod) = break (==' ') (trim result)
      let (path, version) = break (==' ') (ltrim afterMethod)
      case (version == "HTTP/1.1" || version == "HTTP/1.0") of
        False => pure (Just InvalidRequest)
        True => pure $ Just $ ValidRequest $ MkHttpRequest "GET" [] ""
  
    incomingConnectionLoop : (sourceAddr : SocketAddress)
                          -> (rawSock : Var)
                          -> ST m () [remove rawSock (Sock tcpSockets Connected)]
    incomingConnectionLoop sourceAddr rawSock = do
        (sock ** prfSockEquiv) <- initBufferedSocket rawSock
        (rewrite prfSockEquiv in go sock)
        closeBufferedSocket sock
      where
        go : (sock : BufferedSocket) -> ST m (Maybe ()) (maybeBufferedSocketFails {tcpSocketInstance = tcpSockets} {ty = ()} sock)
        go sock = with ST do
          -- TODO: Consider some kind of timeout on incoming connections
          Just (ValidRequest headers) <- readHTTPHeaders sock
            | Nothing => pure Nothing
            | Just InvalidRequest => 
              -- To do: Send a 400 error.
              pure (Just ())
          -- body <- ?readHTTPBody
          -- let req = record { body = body } headers
          go sock

    applicationAcceptLoop : (listener: Var) -> ST m String [listener ::: Sock tcpSockets Listening :-> Sock tcpSockets Failed]
    applicationAcceptLoop listener = do
      -- TODO: Consider some kind of limit on the number of open connections to
      -- avoid a DoS
      Just _ <- accept tcpSockets listener incomingConnectionLoop
        | Nothing => pure "Failed to accept"
      applicationAcceptLoop listener
