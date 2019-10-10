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
            sendResponse specificEngine engineState $
              case path req of
                "/" => MkHttpResponse http200 [] "It works!"
                "/hello" => MkHttpResponse http200 [] "Hello world!"
                _ => MkHttpResponse http404 [] ""

main : IO ()
main = do
  result <- run mainST
  printLn result
