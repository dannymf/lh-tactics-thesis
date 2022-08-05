module Main where

{-@ LIQUID "--compile-spec" @-}

import Building
import Debug
import File
import InlineTactic
import Options
import Parsing
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
    [] -> error $ "This command reqires arguments of the form <filePath>:<defName> <option*>"
    (filePath_defName : strs_opts) -> do
      let options = parseOptions strs_opts
      case splitByChar ':' filePath_defName of
        [filePath] -> do
          filePath <- toGlobalFilePath filePath
          inlineTactics options filePath
          return ()
        [filePath, defName] -> do
          filePath <- toGlobalFilePath filePath
          tacticSplices <- inlineTactics options filePath
          putStrLn $ "[debug] filePath = " ++ show filePath
          putStrLn $ "[debug] defName = " ++ show defName
          putStrLn $ "[debug] tacticSplices = " ++ show tacticSplices
          case filter ((defName ==) . name_TS) tacticSplices of
            [tacticSplice] -> pruneAutos options filePath defName tacticSplice
            _ -> error "not a valid defName"
          return ()
        _ -> do
          error $ "Badly formed input: " ++ show filePath_defName ++ ". It's required to be of the form <filePath>:<defName>"

parseOptions :: [String] -> Options
parseOptions =
  foldl
    ( \opts str -> case str of
        "--write-tactic-dir" -> opts {generate_tactic_dir = True}
        "--write-tactic-encoding" -> opts {generate_tactic_encoding = True}
        _ -> error $ "unrecognized option: '" ++ str ++ "'"
    )
    defaultOptions
