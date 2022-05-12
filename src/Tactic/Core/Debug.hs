{-# LANGUAGE BlockArguments #-}

module Tactic.Core.Debug where

{-@ LIQUID "--compile-spec" @-}

import Control.Monad
import Language.Haskell.TH
import System.IO.Unsafe (unsafePerformIO)

_DEBUG = True

debug :: String -> ()
debug msg =
  unsafePerformIO do
    when _DEBUG $ putStrLn $ "[#] " ++ msg

debugs :: [String] -> ()
debugs msgs =
  unsafePerformIO $
    when _DEBUG do
      putStrLn "[#] {"
      void (traverse putStrLn msgs)
      putStrLn "[#] }"

debugM :: Monad m => String -> m ()
debugM msg =
  when _DEBUG $
    return $! unsafePerformIO do
      putStrLn $ "[#] " ++ msg

debugQ :: String -> Q ()
debugQ msg =
  if _DEBUG
    then runIO $! putStrLn $! "[#] " ++ msg
    else pure ()

debugsM :: Monad m => [String] -> m ()
debugsM msgs =
  return $! unsafePerformIO $
    when _DEBUG do
      putStrLn "[#] {"
      void (traverse putStrLn msgs)
      putStrLn "[#] }"
