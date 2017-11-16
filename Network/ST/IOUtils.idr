module Network.ST.IOUtils

import Control.ST
import Network.ST.TcpSockets
import Control.Funext

export
writeSocketFully : {m : Type -> Type} ->
                   {auto tcpSocketInstance : TcpSockets m} ->
                   (out : String) ->
                   (sock : Var) ->
                   ST m Bool [sock ::: (Sock tcpSocketInstance Connected :-> (\v => if v then Sock tcpSocketInstance Connected else Sock tcpSocketInstance Failed))]
writeSocketFully "" _ = pure True
writeSocketFully {tcpSocketInstance} out sock = with ST do
  case !(writeSocket tcpSocketInstance out sock) of
    Nothing => pure False
    Just out' => writeSocketFully out' sock


export
record IOBuffer (sock : Var) where
  constructor MkIOBuffer
  ioBufferContents : String

public export
record BufferedSocket where
  constructor MkBufferedSocket
  ioSocket, ioBuffer : Var

initIOBuffer : {m : Type -> Type}
               -> {auto tcpSocketInstance : TcpSockets m}
               -> (sock : Var)
               -> ST m Var [add (State $ IOBuffer sock)
                           , sock ::: Sock tcpSocketInstance st]
initIOBuffer sock = new (MkIOBuffer "")

-- export
initBufferedSocket : {m : Type -> Type}
                     -> {auto tcpSocketInstance : TcpSockets m}
                     -> (sock : Var)
                     -> ST m BufferedSocket [
                          Add (\bs : BufferedSocket => [(ioBuffer bs) ::: (State (IOBuffer sock))])
                          , sock ::: Sock tcpSocketInstance st
                        ]
initBufferedSocket sock = with ST do
  ioBuf <- initIOBuffer sock
  pure $ MkBufferedSocket sock ioBuf

export
deleteIOBuffer : {m : Type -> Type}
               -> (sock : Var)
               -> (sockBuffer : Var)
               -> ST m () [remove sockBuffer (State $ IOBuffer sock)]
deleteIOBuffer _ sockBuffer = ST.delete sockBuffer

export
putIOBuffer : {m : Type -> Type}
            -> (sock : BufferedSocket)
            -> String
            -> ST m () [(ioBuffer sock) ::: State (IOBuffer (ioSocket sock))]
putIOBuffer sock newData =
  update (ioBuffer sock) (\buf : IOBuffer (ioSocket sock) => record {
    ioBufferContents = newData ++ (ioBufferContents buf)
  } buf)

export
takeIOBuffer : {m : Type -> Type}
            -> (sock : BufferedSocket)
            -> ST m String [(ioBuffer sock) ::: State (IOBuffer (ioSocket sock))]
takeIOBuffer sock = do
  MkIOBuffer contents <- read (ioBuffer sock)
  write (ioBuffer sock) $ MkIOBuffer ""
  pure contents

export
readFromBufferedSocket : {m : Type -> Type}
                       -> {auto tcpSocketInstance : TcpSockets m}
                       -> (sock : BufferedSocket)
                       -> ST m (Maybe String) [(ioBuffer sock) ::: State (IOBuffer (ioSocket sock)), (ioSocket sock) ::: Sock tcpSocketInstance Connected :-> maybeCaseOnly (Sock tcpSocketInstance Failed) (Sock tcpSocketInstance Connected)]
readFromBufferedSocket {m} {tcpSocketInstance} sock = with ST do
    result <- ST.call (takeIOBuffer sock)
    if result == "" then
      call (readSocket {m} tcpSocketInstance (ioSocket sock))    
    else
      pure (Just result)
    
ifWithProofs : (x : Bool) -> ((x = True) -> a) -> (not x = True -> a) -> a
ifWithProofs True f _ = f Refl
ifWithProofs False _ f = f Refl

-- TODO - We probably want an upper limit on the line length if we are going to use this for HTTP, as otherwise it could have
--        unbounded memory usage.
export
readLineFromSocket : {m : Type -> Type}
                     -> {auto tcpSocketInstance : TcpSockets m}
                     -> (sock : BufferedSocket)
                     -> ST m (Maybe String) [(ioBuffer sock) ::: State (IOBuffer (ioSocket sock)), (ioSocket sock) ::: Sock tcpSocketInstance Connected :-> maybeCaseOnly (Sock tcpSocketInstance Failed) (Sock tcpSocketInstance Connected)]
readLineFromSocket {m} {tcpSocketInstance} sock = go ""
  where
    go : String -> ST m (Maybe String) [
          (ioBuffer sock) ::: State (IOBuffer (ioSocket sock)),
          (ioSocket sock) ::: Sock tcpSocketInstance Connected :-> maybeCaseOnly (Sock tcpSocketInstance Failed) (Sock tcpSocketInstance Connected)]
    go pfx = with ST do
      Just readData <- readFromBufferedSocket {m} {tcpSocketInstance} sock
        | Nothing => pure Nothing
      let (beforeNewline, afterNewline) = break (\x => x == '\n') readData
      ifWithProofs (afterNewline == "")
        (\_ =>
          go (pfx ++ beforeNewline)
        )
        (\proofNotEmpty => do
          call (putIOBuffer {m} sock (strTail' afterNewline proofNotEmpty))
          pure $ Just $ pfx ++ beforeNewline
        )
