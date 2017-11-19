import Network.DefaultHttpEngine
import Control.ST
import Network.Wai
import Network.ST.TcpSockets
import Network.Socket.Data

specificEngine : HttpEngine IO
specificEngine = defaultHttpEngine IO ioTcpSockets

mainST : ST IO String []
mainST = runApplication specificEngine Nothing 8080 $
           mkApplication specificEngine $ \engineState, req => do
            sendResponse specificEngine engineState (MkHttpResponse http200 [] "It works!")

main : IO ()
main = do
  result <- run mainST
  printLn result
