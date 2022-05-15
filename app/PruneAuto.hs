{-# LANGUAGE BlockArguments #-}

{-@ LIQUID "--compile-spec" @-}

module PruneAuto where

import Options
import Building
import Control.Monad as Monad
import Data.Char as Char
import Data.List as List
import Data.Maybe as Maybe
import Data.Serialize
import Debug
import File
import InlineTactic
import Language.Haskell.TH.Ppr
import Language.Haskell.TH.Syntax
import Parsing
import System.IO as IO
import System.IO.Strict (SIO)
import qualified System.IO.Strict as SIO
import System.IO.Unsafe (unsafePerformIO)
import System.Process as Process
import Tactic.Core.PprintPreSyntax
import Tactic.Core.SplicePreSyntax
import Tactic.Core.PreSyntax

{-
  GOAL:

  Remove bad normals:

  For each use of the `auto` tactic, check each normal in isolation for LH errors.
  Only keep the normals that do not have LH errors.
  I.e. discard the normals with LH errors.

  Pruning unused normals:

  For each use of the `auto` tactic, does binary search to find
  the smallest subset of generated normals that still pass TH check.
  I.e. discard the unused normals.
-}

{-
  ! OLD
  PROCESS:
  - get TH spliced output
  - make copy of input file with TH spliced output in designated location
  - prune bad normals (at each `auto` site):
    - replace `auto` site with `undefined`
    - loop:
      - replaces `auto` site with the next normal combined with `undefined`
        (in a way that the undefined is not available in the refinement of the use)
      - run LH check
        - if passes LH check, then mark normal as _good_
        - if fails LH check, then mark normal as _bad_
    - only keep the _good_ normals
  - prune unused normals (at each `auto` site):
    - loop1
      - select entire `auto` site as current site
        - prune 1/2 subset of normals in current site
        - loop2
          - run LH check
            - if passes, then loop1
            - if fails, then select next 1/2 subset of normals, then loop2
-}

{-
  PROCESS
  - find original tactic source file (in .tactic)
  - for each tactic dec:
    - parse the tactic to PreExp
    - the pruning only takes place at each AutoPreExp, so focus on those
    - do pruning procedure on each AutoPreExp cite until found minimal set of
      neutrals, where the pruning is done on the AutoPreExp and then is spliced to
      Exp which is spliced into the program file
-}

pruneAutos :: Options -> FilePath -> String -> TacticSplice -> IO ()
pruneAutos options filePath defName tacticSplice = do
  consoleIO $ "pruning autos in module " ++ show filePath ++ " in definition " ++ show defName
  Just str_err <- build defaultOptions_build {capture_std_err = True, checkLH = True}
  if passesLH str_err
    then do
      -- [tacticEncoding] <- id $! lines <$> readFile (moduleFilePath_to_tacticEncodingFilePath filePath defName)
      let tacticEncoding = encoding_TS tacticSplice
      let preDec = decode_ tacticEncoding :: PreDec
      loop preDec
    else putStrLn $ "Prune autos error: Must pass LH before pruning autos:\n\n" ++ str_err
  where
    loop :: PreDec -> IO ()
    loop (PreDec x t pe) = do
      case pruneNext pe of
        Just pe' -> do
          putStrLn "Prune autos: trying prune"
          inlinePreDec (PreDec x t pe')
          Just str_err <- build defaultOptions_build {capture_std_err = True, checkLH = True}
          show str_err `seq` do
            -- TODO: nope, still locked
            if passesLH str_err
              then do
                putStrLn "Prune autos: prune success"
                loop (PreDec x t pe')
              else do
                putStrLn "Prune autos: prune failure, instead keep that exp"
                case keepNext pe of
                  Just pe' -> loop (PreDec x t pe')
                  Nothing -> do
                    putStrLn "Prune autos: done"
                    inlinePreDec (PreDec x t pe) -- done
        Nothing -> do
          putStrLn "Prune autos: done"
          inlinePreDec (PreDec x t pe) -- done

    -- replaces appropriate lines with spliced PreDec
    inlinePreDec :: PreDec -> IO ()
    inlinePreDec preDec = do
      -- TODO: problem: file is still locked at this readFile (pretty sure its this one)
      -- probably has something to do with `build` being lazy since its normal IO

      -- str_src <- readFile filePath
      putStrLn "preDec:"
      print preDec

      (_, Just hdl_out, _, hdl_proc) <-
        createProcess $
          (shell . unwords $ ["cat", filePath])
            { std_out = CreatePipe
            }
      -- waitForProcess hdl_proc -- ! probably causes hang for some reason
      str_src <- hGetContents hdl_out

      let ls_src = lines str_src
      -- putStrLn "ls_src:"
      -- print ls_src

      let mb_str_src' = do
            (ls_before, (l_begin : ls_between)) <- splitAtFindIndex (("-- %tactic:begin:" ++ defName) ==) ls_src
            (_, (l_end : ls_after)) <- splitAtFindIndex (("-- %tactic:end:" ++ defName) ==) ls_between
            let ls_new = lines (pprint (splicePreDec preDec)) -- ! OLD: using TH.Ppr.pprint
            -- let ls_new = lines (pprintPreDec preDec) -- ! NEW: using my custom Tactic.Core.PprintPreSyntax
            let str_src' = unlines . concat $ [ls_before, [l_begin], ls_new, [l_end], ls_after]
            Just str_src'

      case mb_str_src' of
        Just str_src' -> do
          writeFile filePath str_src'
        Nothing ->
          error $ "Prune auto error: cannot bind %tactic-delimited zone in source file:\n" ++ str_src

pruneNext :: PreExp -> Maybe PreExp
pruneNext (Lambda x pe) = Lambda x <$> pruneNext pe
pruneNext (Case e ms) = Case e <$> go ms
  where
    go :: [(Pat, PreExp)] -> Maybe [(Pat, PreExp)]
    go [] = Nothing
    go ((p, pe) : ms) = case pruneNext pe of
      Just pe' -> Just ((p, pe') : ms)
      Nothing -> ((p, pe) :) <$> go ms
pruneNext (If e pe1 pe2) = case pruneNext pe1 of
  Just pe1' -> Just $ If e pe1' pe2
  Nothing -> If e pe1 <$> pruneNext pe2
pruneNext (Exp e pe) = Exp e <$> pruneNext pe
pruneNext (AutoPreExp es st pe) =
  case es of
    [] -> AutoPreExp es st <$> pruneNext pe
    (e : es) -> Just (AutoPreExp es (st {pruned = e : pruned st}) pe)
pruneNext (TrivialPreExp) = Nothing

keepNext :: PreExp -> Maybe PreExp
keepNext (Lambda x pe) = Lambda x <$> keepNext pe
keepNext (Case e ms) = Case e <$> go ms
  where
    go :: [(Pat, PreExp)] -> Maybe [(Pat, PreExp)]
    go [] = Nothing
    go ((p, pe) : ms) = case keepNext pe of
      Just pe' -> Just ((p, pe') : ms)
      Nothing -> ((p, pe) :) <$> go ms
keepNext (If e pe1 pe2) = case keepNext pe1 of
  Just pe1' -> Just $ If e pe1' pe2
  Nothing -> If e pe1 <$> keepNext pe2
keepNext (Exp e pe) = Exp e <$> keepNext pe
keepNext (AutoPreExp es st pe) =
  case es of
    [] -> AutoPreExp es st <$> keepNext pe
    (e : es) -> Just (AutoPreExp es (st {kept = e : kept st}) pe)
keepNext (TrivialPreExp) = Nothing

-- analyzes std_err output to see if LH succeeded
passesLH :: String -> Bool
passesLH str = unsafePerformIO do
  if isJust $ splitAtPrefix "LIQUID: UNSAFE" str
    then do
      putStrLn $ "FAILS LH"
      return False
    else
      if isJust $ splitAtPrefix "error:" str
        then do
          error $ "FAiLS GHC:\n" ++ str
        else do
          putStrLn $ "PASSES LH & GHC"
          return True

{-
faster pruning:
at each auto:
  exps = all exps of auto
  -- there are still unprocessed (i.e. not kept or discarded) exps:
  loop(exps) where
  loop(exps):
    if exps is singleton then
      keep exps
    else
      prune half#1 of exps 
      if PASS then
        discard half#1
        loop
      else
        unprune half#1
        prune half#2
        if PASS then
          discard half#2
          loop
        else
          unprune half#2
          loop(half#1)
          loop(half#2)
-}