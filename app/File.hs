{-# LANGUAGE BlockArguments #-}

module File where 

import Parsing
import Control.Monad as Monad
import Data.Char as Char
import Data.List as List
import Data.Maybe as Maybe
import Debug
import System.IO as IO
import System.Process as Process

toGlobalFilePath :: FilePath -> IO FilePath
toGlobalFilePath filePath = do
  pwd <- trimSpace <$> readProcess "pwd" [] ""
  return $ pwd ++ "/" ++ filePath

getDirSize :: FilePath -> IO Int 
getDirSize filePath = length . lines <$> readProcess "ls" [filePath] ""

moduleFilePath_to_tacticDir :: FilePath -> FilePath 
moduleFilePath_to_tacticDir filePath = filePath ++ ".tactic/"

moduleFilePath_to_tacticEncodingFilePath :: FilePath -> String -> FilePath
moduleFilePath_to_tacticEncodingFilePath filePath defName = filePath ++ "." ++ defName ++ ".tactic-encoding" 

-- TODO: check that mkdir was successful 
mkdir :: FilePath -> IO Bool
mkdir filePath = do 
  system $ "mkdir " ++ filePath
  return True

-- TODO: check that mv was successful
mv :: FilePath -> FilePath -> IO Bool
mv filePath filePath' = do 
  system $ "mv " ++ filePath ++ " " ++ filePath'
  return True
