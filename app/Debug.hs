{-# LANGUAGE BlockArguments #-}

module Debug where

import System.IO.Strict (SIO)
import qualified System.IO.Strict as SIO
import Control.Monad

debugIO :: String -> IO ()
debugIO msg = when True do
  if length (lines msg) == 1 then 
    putStrLn $ "[debug] " ++ msg 
  else do 
    putStrLn $ "[debug] " ++ replicate 40 '='
    putStrLn msg

consoleIO :: String -> IO ()
consoleIO msg = when True do 
  if length (lines msg) == 1 then 
    putStrLn $ "[console] " ++ msg 
  else do 
    putStrLn $ "[console] " ++ replicate 40 '='
    putStrLn msg


consoleSIO :: String -> SIO ()
consoleSIO msg = when True do 
  if length (lines msg) == 1 then 
    SIO.putStrLn $ "[console] " ++ msg 
  else do 
    SIO.putStrLn $ "[console] " ++ replicate 40 '='
    SIO.putStrLn msg
