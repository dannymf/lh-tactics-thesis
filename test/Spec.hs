import qualified Test1
import qualified Test2

main :: IO ()
main = do
  putStrLn ""
  putStrLn "==================================================================="
  Test1.main
  -- Test2.main
  pure ()
