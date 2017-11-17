module Network.ST.IOUtils

import Control.ST
import Network.ST.TcpSockets
import Control.Funext
import Data.Nat.NatTheorems

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

export total
initBufferedSocket : {m : Type -> Type}
                     -> {auto tcpSocketInstance : TcpSockets m}
                     -> (sock : Var)
                     -> ST m (bufSock : BufferedSocket ** (sock = ioSocket bufSock)) [
                          Add (\bs => [(ioBuffer $ fst $ bs) ::: (State (IOBuffer sock))])
                          , sock ::: Sock tcpSocketInstance st
                        ]
initBufferedSocket sock = with ST do
  ioBuf <- initIOBuffer sock
  pure $ ((MkBufferedSocket sock ioBuf) ** Refl)

export total
deleteIOBuffer : {m : Type -> Type}
               -> (sock : Var)
               -> (sockBuffer : Var)
               -> ST m () [remove sockBuffer (State $ IOBuffer sock)]
deleteIOBuffer _ sockBuffer = ST.delete sockBuffer

export total
closeBufferedSocket : {m : Type -> Type}
                    -> {auto tcpSocketInstance : TcpSockets m}
                    -> (sock : BufferedSocket)
                    -> ST m () [ remove (ioBuffer sock) (State $ IOBuffer (ioSocket sock))
                               , remove (ioSocket sock) (Sock tcpSocketInstance st)]
closeBufferedSocket {tcpSocketInstance} sock = do
  call $ deleteIOBuffer (ioSocket sock) (ioBuffer sock)
  call $ close tcpSocketInstance (ioSocket sock)

export total
putIOBuffer : {m : Type -> Type}
            -> (sock : BufferedSocket)
            -> String
            -> ST m () [(ioBuffer sock) ::: State (IOBuffer (ioSocket sock))]
putIOBuffer sock newData =
  update (ioBuffer sock) (\buf : IOBuffer (ioSocket sock) => record {
    ioBufferContents = newData ++ (ioBufferContents buf)
  } buf)

export total
takeIOBuffer : {m : Type -> Type}
            -> (sock : BufferedSocket)
            -> ST m String [(ioBuffer sock) ::: State (IOBuffer (ioSocket sock))]
takeIOBuffer sock = do
  MkIOBuffer contents <- read (ioBuffer sock)
  write (ioBuffer sock) $ MkIOBuffer ""
  pure contents

public export total
%error_reduce -- always evaluate this before showing errors
maybeBufferedSocketFails : {auto tcpSocketInstance : TcpSockets m} -> {ty : Type} -> (sock : BufferedSocket) -> List (Action (Maybe ty))
maybeBufferedSocketFails {tcpSocketInstance} {ty} sock = [
    (ioBuffer sock) ::: State (IOBuffer (ioSocket sock))
  , (ioSocket sock) ::: (Sock tcpSocketInstance Connected :-> wrappedMaybeCaseOnly (Sock tcpSocketInstance) Failed Connected)
  ]

export total
readFromBufferedSocket : {m : Type -> Type}
                       -> {auto tcpSocketInstance : TcpSockets m}
                       -> (sock : BufferedSocket)
                       -> ST m (Maybe String) (maybeBufferedSocketFails sock)
readFromBufferedSocket {m} {tcpSocketInstance} sock = with ST do
    result <- ST.call (takeIOBuffer sock)
    if result == "" then
      call (readSocket {m} tcpSocketInstance (ioSocket sock))    
    else
      pure (Just result)
    
export total
ifWithProofs : (x : Bool) -> ((x = True) -> a) -> (not x = True -> a) -> a
ifWithProofs True f _ = f Refl
ifWithProofs False _ f = f Refl

-- TODO - We probably want an upper limit on the line length if we are going to use this for HTTP, as otherwise it could have
--        unbounded memory usage.
export
readLineFromSocket : {m : Type -> Type}
                     -> {auto tcpSocketInstance : TcpSockets m}
                     -> (sock : BufferedSocket)
                     -> ST m (Maybe String) (maybeBufferedSocketFails sock)
readLineFromSocket {m} {tcpSocketInstance} sock = go ""
  where
    go : String -> ST m (Maybe String) [
          (ioBuffer sock) ::: State (IOBuffer (ioSocket sock)),
          (ioSocket sock) ::: Sock tcpSocketInstance Connected :-> wrappedMaybeCaseOnly (Sock tcpSocketInstance) Failed Connected]
    go pfx = with ST do
      Just readData <- readFromBufferedSocket {m} {tcpSocketInstance} sock
        | Nothing => pure Nothing
      let (beforeNewline, afterAndIncludingNewline) = break (\x => x == '\n') readData
      ifWithProofs (afterAndIncludingNewline == "")
        (\_ =>
          go (pfx ++ beforeNewline)
        )
        (\proofNotEmpty => do
          call (putIOBuffer {m} sock (strTail' afterAndIncludingNewline proofNotEmpty))
          pure $ Just $ pfx ++ beforeNewline
        )      

export
readFullyFromSocket : {m : Type -> Type}
                      -> {auto tcpSocketInstance : TcpSockets m}
                      -> (readLength : Nat)
                      -> (sock : BufferedSocket)
                      -> ST m (Maybe String) (maybeBufferedSocketFails sock)
readFullyFromSocket {m} {tcpSocketInstance} l sock = go l ""
  where
    go : (remaining : Nat) -> String -> ST m (Maybe String) (maybeBufferedSocketFails sock)
    go Z s = pure $ Just s
    go remaining pfx = with ST do
      Just readData <- readFromBufferedSocket {m} {tcpSocketInstance} sock
        | Nothing => pure Nothing
      let dataLen : Nat = length readData
      ifWithProofs (dataLen < remaining)
        (\proofLt =>
          let
            prfComparison : LTE dataLen remaining = natALTBImpliesALTEB dataLen remaining (natALtBIsTrueImpliesLTAB dataLen remaining proofLt)
          in
            go (remaining - dataLen) (pfx ++ readData)
        )
        (\proofNotLt => with ST do
          let prfComparison : LTE remaining dataLen =
            natALtBIsFalseImpliesGTEAB dataLen remaining (NotAEqNotBImpliesAEqB (dataLen < remaining) False proofNotLt)
          call $ putIOBuffer {m} sock (substr remaining (dataLen - remaining) readData)
          pure $ Just $ pfx ++ substr 0 remaining readData
        )
