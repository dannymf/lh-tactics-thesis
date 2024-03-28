{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE NamedFieldPuns #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Core.SplicePreSyntax where

import qualified Data.List as List
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Ppr (pprint)
import qualified Language.Haskell.TH.Quote as Quote
import Language.Haskell.TH.Syntax hiding (lift)
import Proof
import Tactic.Core.Debug
import Tactic.Core.PreSyntax
import Tactic.Core.Syntax
import Tactic.Core.Utility
import Prelude hiding (exp)

-- splicePreExp :: PreExp -> Q Exp
-- splicePreExp (Lambda x pe) = [|\ $(varP x) -> $(splicePreExp pe)|]
-- splicePreExp (Case e ms) = caseE (pure e) ((\(p, pe) -> match (pure p) (normalB (splicePreExp pe)) []) <$> ms)
-- splicePreExp (If e pe1 pe2) = condE (pure e) (splicePreExp pe1) (splicePreExp pe2)
-- splicePreExp (Exps es pe) = do
--   e <- splicePreExp pe
--   conjunction (es <> [e])
-- splicePreExp (TrivialPreExp) = [|trivial|]

-- splicePreDec :: PreDec -> Q [Dec]
-- splicePreDec (PreDec x t pe) =

splicePreExp :: PreExp -> Exp
splicePreExp (Lambda x pe) = LamE [VarP x] (splicePreExp pe)
splicePreExp (Case e ms) = CaseE e ((\(p, pe) -> Match p (NormalB (splicePreExp pe)) []) <$> ms)
splicePreExp (If e pe1 pe2) = CondE e (splicePreExp pe1) (splicePreExp pe2)
splicePreExp (Exp e TrivialPreExp) = e
splicePreExp (Exp e pe) = conjunctionExp [e, splicePreExp pe]
splicePreExp (AutoPreExp es (PruneAutoState {kept}) TrivialPreExp) = conjunctionExp (es <> kept)
splicePreExp (AutoPreExp es (PruneAutoState {kept}) pe) = conjunctionExp (es <> kept <> [splicePreExp pe])
splicePreExp TrivialPreExp = VarE (mkName "trivial")

splicePreDec :: PreDec -> [Dec]
splicePreDec (PreDec x t pe) =
  [ SigD x t,
    FunD x [Clause [] (NormalB (splicePreExp pe)) []]
  ]
