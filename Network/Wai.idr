module Network.Wai
import Control.ST
import Network.ST.TcpSockets
import Network.ST.IOUtils
import Network.Socket.Data
import Data.Bool.BoolTheorems
import Data.String.StringUtils

export
PendingRequest : (socks : TcpSockets m) -> Type
PendingRequest socks = Composite [ 
                                   State (sock: BufferedSocket ** (IOBuffer (ioSocket sock)))
                                 , CFSock socks
                                 ]

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
  body : String

public export
data InvalidRequestOr : a -> Type where
  ValidRequest : a -> InvalidRequestOr a
  InvalidRequest : InvalidRequestOr a

public export
record HttpEngine (m : Type -> Type) where
  constructor MkHttpEngine
  Application : Type
  EngineState : Type
  httpEngineActions : EngineState -> (ty : Type) -> List (Action ty)
  pendingRequestVar : EngineState -> Var
  PendingRequest : Type
  sendResponse : (engineState: EngineState) -> HttpResponse ->
                     ST m () ((remove (pendingRequestVar engineState) PendingRequest)::
                              (httpEngineActions engineState ()))
  mkApplication : ((engineState : EngineState) ->
                   HttpRequest ->
                   ST m () ((remove (pendingRequestVar engineState) PendingRequest)::
                            (httpEngineActions engineState ()))
                  ) -> Application
  runApplication : (bindTo: Maybe SocketAddress) -> (port: Int) ->
                   (app: Application) -> ST m String []

export
getHttpHeader : (wantedHeaderName : String) -> (req : HttpRequest) -> Maybe HttpHeader
getHttpHeader hn req = find (\h => toLower (headerName h) == toLower hn) (headers req)

record DefaultHttpEngineState where
  constructor MkDefaultHttpEngineState
  enginePendingRequestVar : Var
  engineBufferedSocket : BufferedSocket

DefaultHttpPendingRequest : Type
DefaultHttpPendingRequest = State ()

%error_reduce
defaultHttpEngineActions : {tcpSockets: TcpSockets m} -> DefaultHttpEngineState -> (ty : Type) -> List (Action ty)
defaultHttpEngineActions {tcpSockets} st ty =
    [ioBuffer (engineBufferedSocket st) ::: State (IOBuffer $ ioSocket (engineBufferedSocket st)),
     ioSocket (engineBufferedSocket st) ::: CFSock tcpSockets]

data DefaultHttpApplication : (m : Type -> Type) -> (tcpSockets: TcpSockets m) -> Type where
  MkDefaultHttpApplication :
    ((engineState : DefaultHttpEngineState) -> HttpRequest
       -> ST m () ((remove (enginePendingRequestVar engineState) DefaultHttpPendingRequest)::(defaultHttpEngineActions {tcpSockets} engineState ()))) -> DefaultHttpApplication m tcpSockets

joinByCRLF : List String -> String
joinByCRLF args =
    go "" args
  where
    go : String -> List String -> String
    go pfx [] = pfx
    go pfx (h::t) = go (pfx ++ h ++ "\n") t

httpHeaderToString : HttpHeader -> String
httpHeaderToString (MkHttpHeader n v) =
  n ++ ": " ++ v

httpResponseToString : HttpResponse -> String
httpResponseToString resp =
  joinByCRLF $ 
   ("HTTP/1.1 " ++ (show . responseNumber . code $ resp) ++ " " ++
    (show . responseText . code $ resp))::
   ((map httpHeaderToString
         ((MkHttpHeader "Content-Length" (show . Strings.length . body $ resp)) ::
          (headers resp))) ++ ["", body resp])

defaultHttpEngineSendResponse : (m : Type -> Type) -> (tcpSockets: TcpSockets m)
    -> (engineState: DefaultHttpEngineState)
    -> HttpResponse
    -> ST m () ((remove (enginePendingRequestVar engineState) DefaultHttpPendingRequest)::
                              (defaultHttpEngineActions {m} {tcpSockets} engineState ()))
defaultHttpEngineSendResponse m tcpSockets st resp =
     with ST do
       delete (enginePendingRequestVar st)
       True <- call $ fromCFSock tcpSockets (ioSocket (engineBufferedSocket st))
         | False => with ST do
             call $ toCFSock tcpSockets Failed Refl (ioSocket (engineBufferedSocket st))
             pure ()
       True <- call $ writeSocketFully {m} {tcpSocketInstance = tcpSockets}
                (httpResponseToString resp)
                (ioSocket (engineBufferedSocket st))
         | False => with ST do
             call $ toCFSock tcpSockets Failed Refl (ioSocket (engineBufferedSocket st))
             pure ()       
       call $ toCFSock tcpSockets Connected Refl (ioSocket (engineBufferedSocket st))


defaultHttpEngineRunApplication : {m : Type -> Type}
                 -> {tcpSockets: TcpSockets m}
                 -> (bindTo: Maybe SocketAddress)
                 -> (port: Int)
                 -> (app: DefaultHttpApplication m tcpSockets)
                 -> ST m String []
defaultHttpEngineRunApplication {m} {tcpSockets} bindTo port app =
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
  
    runAppCall : (sock : BufferedSocket) -> HttpRequest -> DefaultHttpApplication m tcpSockets -> ST m (Maybe ()) (maybeBufferedSocketFails {tcpSocketInstance = tcpSockets} {ty = ()} sock)
    runAppCall sock req (MkDefaultHttpApplication appFn) =
        with ST do
          call $ toCFSock tcpSockets Connected Refl (ioSocket sock)
          pendingRequest <- new ()
          let engineState : DefaultHttpEngineState = MkDefaultHttpEngineState pendingRequest sock
          appFn engineState req
          let engineBufferedSocketPrf : (engineBufferedSocket engineState = sock) = Refl
          doFromCFSock
      where
        doFromCFSock : ST m (Maybe ()) [
            (ioBuffer sock) ::: State (IOBuffer (ioSocket sock))
          , ioSocket sock ::: (CFSock tcpSockets) :-> wrappedMaybeCaseOnly (Sock tcpSockets) Failed Connected
        ]
        doFromCFSock = with ST do
          True <- call $ fromCFSock tcpSockets (ioSocket sock)
          | False => pure Nothing
          pure (Just ())
  
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
          Just _ <- runAppCall sock req app
            | Nothing => pure Nothing
          go sock

    applicationAcceptLoop : (listener: Var) -> ST m String [listener ::: Sock tcpSockets Listening :-> Sock tcpSockets Failed]
    applicationAcceptLoop listener = do
      -- TODO: Consider some kind of limit on the number of open connections to
      -- avoid a DoS
      Just _ <- accept tcpSockets listener incomingConnectionLoop
        | Nothing => pure "Failed to accept"
      applicationAcceptLoop listener

defaultHttpEngine : (m : Type -> Type) -> (tcpSockets : TcpSockets m) -> HttpEngine m
defaultHttpEngine m tcpSockets = MkHttpEngine
  {- Application -} (DefaultHttpApplication m tcpSockets)
  {- EngineState -} DefaultHttpEngineState
  {- httpEngineActions -} defaultHttpEngineActions
  {- pendingRequestVar -} enginePendingRequestVar
  {- PendingRequest -} DefaultHttpPendingRequest
  {- sendResponse -} (defaultHttpEngineSendResponse m tcpSockets)
  {- mkApplication -} MkDefaultHttpApplication
  {- runApplication -} (defaultHttpEngineRunApplication {m} {tcpSockets})
