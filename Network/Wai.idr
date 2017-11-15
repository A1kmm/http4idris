module Network.Wai
import Control.ST
import Network.Socket

data PendingRequest = MkPendingRequest

data Request = MkRequest
data Response = MkResponse

interface CanRespondHTTP (m : Type -> Type) where
  responseHttp : Response -> ST m () [remove pendingRequest PendingRequest]

data Application : (m : Type -> Type) -> Type where
  MkApplication : ((pendingRequest : Var) -> (Response -> ST m () [remove pendingRequest PendingRequest]) 
                   -> (req : Request) -> ST m () [remove pendingRequest PendingRequest])
                   -> Application m


{-
openSocket : Application IO -> ST IO (Maybe Socket) 

runServer : Application IO -> ST IO Boolean [] = with ST do
  Right socket <- lift $ socket AF_INET6 Stream 0
    | Left _ => pure False
  haveSocket <- 
-}
