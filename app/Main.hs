module Main where

{-@ LIQUID "--compile-spec" @-}

import Building
import Debug
import File
import InlineTactic
import PruneAuto
import System.Environment as Environment
import System.Process as Process

main = do
  -- consoleIO "cleaning..."
  -- clean
  -- consoleIO "building..."
  -- mb_result <- build (defaultOptions_build {ddump_splices = True, capture_std_err = True})
  -- consoleIO $ "mb_result: " ++ show mb_result
  -- return ()

  args <- getArgs
  case args of
    [filePath] -> do
      filePath <- toGlobalFilePath filePath
      inlineTactics filePath
      return ()
    [filePath, defName] -> do
      filePath <- toGlobalFilePath filePath
      (_, tacticSplices) <- inlineTactics filePath
      case filter ((defName ==) . name_TS) tacticSplices of 
        [tacticSplice] -> pruneAutos filePath defName tacticSplice
        _ -> error "not a valid defName"
      return ()
    _ -> error "Wrong number of arguments. Requirese "
