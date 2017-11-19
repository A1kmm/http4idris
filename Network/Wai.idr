module Network.Wai
import Control.ST
import Network.Socket.Data

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

export
http200 : HttpResponseCode
http200 = MkHttpResponseCode 200 "OK"
