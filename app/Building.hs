{-# LANGUAGE BlockArguments #-}

module Building where

import Control.Monad as Monad
import Data.Char as Char
import Data.List as List
import Data.Maybe as Maybe
import File
import System.IO as IO
import System.Process as Process

clean :: IO ()
clean = do
  system "stack clean"
  return ()

data Options_build = Options_build
  { ddump_splices :: Bool,
    checkLH :: Bool,
    capture_std_err :: Bool
  }

defaultOptions_build =
  Options_build
    { ddump_splices = False,
      checkLH = False,
      capture_std_err = False
    } ::
    Options_build

build :: Options_build -> IO (Maybe String)
build options = do
  let ghc_options :: [String]
      ghc_options =
        concat
          [ if ddump_splices options then ["-ddump-splices"] else [],
            if checkLH options then ["-fplugin=LiquidHaskell"] else ["-fplugin-opt=LiquidHaskell:--compile-spec"]
          ]
  mb_hdl_err <- do
    (_, _, mb_hdl_err, ph) <-
      createProcess $
        ( shell . unwords . concat $
            [ ["stack build"],
              ["--fast"], -- ? does this break TH somehow?
              if not (null ghc_options) then ["--ghc-options \"" ++ unwords ghc_options ++ "\""] else []
            ]
        )
          { std_err = if capture_std_err options then CreatePipe else Inherit
          }
    -- waitForProcess ph -- TODO: does this make it hang again??
    return mb_hdl_err
  case mb_hdl_err of
    Just hdl_err -> Just <$> hGetContents hdl_err
    Nothing -> return Nothing
