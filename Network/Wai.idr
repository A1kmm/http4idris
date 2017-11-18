module Network.Wai
import Control.ST
import Network.ST.TcpSockets
import Network.ST.IOUtils
import Network.Socket.Data
import Data.Bool.BoolTheorems
import Data.String.StringUtils

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
getHttpHeader : (wantedHeaderName : String) -> (req : HttpRequest) -> Maybe HttpHeader
getHttpHeader hn req = find (\h => toLower (headerName h) == toLower hn) (headers req)

export
runApplication : (m : Type -> Type)
                 -> {tcpSockets: TcpSockets m}
                 -> (bindTo: Maybe SocketAddress)
                 -> (port: Int)
                 -> (app: Application m)
                 -> ST m String []
runApplication m {tcpSockets} bindTo port (MkApplication appFn) =
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
    rtrim : String -> String
    rtrim = reverse . ltrim . reverse
    readHTTPHeaders : (sock : BufferedSocket) -> List HttpHeader -> ST m (Maybe (InvalidRequestOr (List HttpHeader))) (maybeBufferedSocketFails {tcpSocketInstance = tcpSockets} {ty = (InvalidRequestOr (List HttpHeader))} sock)
    readHTTPHeaders sock otherHeaders = do
      Just line <- readLineFromSocket sock
        | Nothing => pure Nothing
      if line == "" then
        pure $ Just $ ValidRequest otherHeaders
      else do
        let (headerNameUntrimmed, headerValueWithPfx) = break (==':') line
        ifWithProofs (headerValueWithPfx == "")
          (\_ => pure $ Just $ InvalidRequest)
          (\prfNonEmpty => do
            let headerName = rtrim headerNameUntrimmed
            let headerValue = trim (strTail' headerValueWithPfx prfNonEmpty)
            readHTTPHeaders sock (MkHttpHeader headerName headerValue :: otherHeaders)
          )
  
    readHTTPHead : (sock : BufferedSocket) ->
                      ST m (Maybe (InvalidRequestOr HttpRequest)) (maybeBufferedSocketFails {tcpSocketInstance = tcpSockets} {ty = (InvalidRequestOr HttpRequest)} sock)
    readHTTPHead sock = with ST do
      Just result <- readLineFromSocket sock
        | Nothing => pure Nothing
      let (method, afterMethod) = break (==' ') (trim result)
      let (path, versionAndSpace) = break (==' ') (ltrim afterMethod)
      let version = ltrim versionAndSpace
      Just (ValidRequest httpHeaders) <- readHTTPHeaders sock []
        | Nothing => pure Nothing
        | Just InvalidRequest => pure (Just InvalidRequest)
      -- TODO: HTTP/2
      if (version == "HTTP/1.1" || version == "HTTP/1.0")
        then pure $ Just $ ValidRequest $ MkHttpRequest method httpHeaders ""
        else pure (Just InvalidRequest)
  
    withContentLength : HttpRequest -> Maybe Nat
    withContentLength req = do
      contentLengthStr <- getHttpHeader "Content-Length" req
      cast (headerValue contentLengthStr)
  
    readHTTPBody : (sock : BufferedSocket) -> (req : HttpRequest) ->
                      ST m (Maybe String) (maybeBufferedSocketFails {tcpSocketInstance = tcpSockets} {ty = String} sock)
    readHTTPBody sock req =
      case withContentLength req of
        Nothing => pure $ Just ""
        Just contentLength =>
          readFullyFromSocket {tcpSocketInstance = tcpSockets} contentLength sock
  
    e400Content : String
    e400Content = "Your browser sent a request the server couldn't understand."
    e400Msg : String
    e400Msg = "HTTP/1.1 400 Bad Request\r\nContent-Length: " ++ (show e400Content)
               ++ "\r\n\r\n" ++ e400Content
  
    send400 : (sock : BufferedSocket) -> ST m (Maybe ()) (maybeBufferedSocketFails {tcpSocketInstance = tcpSockets} {ty = ()} sock)
    send400 sock = do
      True <- call (writeSocketFully {m} {tcpSocketInstance = tcpSockets}
                     e400Msg (ioSocket sock))
        | False => pure Nothing
      pure $ Just ()
  
    runAppCall : ((pendingRequest : Var) -> ST m () [remove pendingRequest PendingRequest]) -> ST m (Maybe ()) (maybeBufferedSocketFails {tcpSocketInstance = tcpSockets} {ty = ()} sock)
  
    sendResponse : HttpResponse -> ST m () [remove pendingRequest PendingRequest]
  
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
          Just (ValidRequest headers) <- readHTTPHead sock
            | Nothing => pure Nothing
            | Just InvalidRequest => 
              send400 sock
          Just body <- readHTTPBody sock headers
            | Nothing => pure Nothing
          let req = record { body = body } headers
          Just _ <- runAppCall (\pendingReq => appFn pendingReq sendResponse req)
            | Nothing => pure Nothing
          go sock

    applicationAcceptLoop : (listener: Var) -> ST m String [listener ::: Sock tcpSockets Listening :-> Sock tcpSockets Failed]
    applicationAcceptLoop listener = do
      -- TODO: Consider some kind of limit on the number of open connections to
      -- avoid a DoS
      Just _ <- accept tcpSockets listener incomingConnectionLoop
        | Nothing => pure "Failed to accept"
      applicationAcceptLoop listener
