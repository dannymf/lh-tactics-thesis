{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Core.Quote where

import Control.Monad.Except
import Control.Monad.State
import Data.Serialize
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Ppr (pprint)
import qualified Language.Haskell.TH.Quote as Quote
import Language.Haskell.TH.Syntax
import System.IO.Unsafe
import Tactic.Core.Debug
import Tactic.Core.Parse
import Tactic.Core.PreSyntax
import qualified Tactic.Core.SplicePreSyntax as SplicePreSyntax
import qualified Tactic.Core.SpliceSyntax as SpliceSyntax
import Tactic.Core.Syntax

tactic :: Quote.QuasiQuoter
tactic =
  Quote.QuasiQuoter
    { Quote.quoteExp = undefined, -- quoteExp,
      Quote.quoteDec = quoteDec,
      Quote.quotePat = error "cannot quote a pattern with tactic quasiquoter",
      Quote.quoteType = error "cannot quote a type with tactic quasiquoter"
    }

-- * old version that spliced directly to Exp

-- quoteExp :: String -> Q Exp
-- quoteExp str = do
--   instrs <- runParser parseInstrs str
--   evalStateT (spliceExp instrs) emptyEnvironment

-- quoteDec :: String -> Q [Dec]
-- quoteDec str = do
--   (env, instrs) <- runParser parseDecInstrs str
--   debugM $ "====================================="
--   debugM $ "instrs: " ++ show instrs
--   debugM $ "env: " ++ show env
--   decs <- evalStateT (spliceDec instrs) env
--   pure decs

-- * new version that splices first to PreExp then to Exp

-- quoteExp :: String -> Q Exp
-- quoteExp str = do
--   instrs <- runParser parseInstrs str
--   -- splice [Instr] to PreExp
--   pe <- evalStateT (SpliceSyntax.spliceExp instrs) emptyEnvironment
--   -- splice PreExp to Exp
--   let e = SplicePreSyntax.splicePreExp pe
--   --
--   pure e

quoteDec :: String -> Q [Dec]
quoteDec str = do
  (env, instrs) <- runParser parseDecInstrs str
  debugM $ "====================================="
  debugM $ "instrs: " ++ show instrs
  debugM $ "env: " ++ show env
  -- splice [Instr] to PreDec
  preDec <- evalStateT (SpliceSyntax.spliceDec instrs) env
  -- splice PreDec to [Dec]
  let decs = SplicePreSyntax.splicePreDec preDec
  -- dummy definition of encoded PreDec
  let decPreDecEnc =
        FunD
          (mkName ("_tactic_encoding_" ++ pprint (def_name env)))
          [Clause [] (NormalB (LitE (StringL (encode preDec)))) []]
  --
  debugM "preDec:"
  debugM (show preDec)
  debugM "decPreDecEnc:"
  debugM (pprint decPreDecEnc)
  --
  pure (decs <> [decPreDecEnc])
  