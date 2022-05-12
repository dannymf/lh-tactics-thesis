{-@ LIQUID "--compile-spec" @-}

module Tactic.Core.PprintPreSyntax where

import qualified Data.List as List
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Ppr (pprint)
import qualified Language.Haskell.TH.Quote as Quote
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Syntax hiding (lift)
import Proof
import Tactic.Core.Debug
import Tactic.Core.PreSyntax
import Tactic.Core.Syntax
import Tactic.Core.Utility
import Prelude hiding (exp)

indent :: Int -> String
indent i = "\n" ++ concat (replicate i "  ")

pprintPreExp :: Int -> PreExp -> String
pprintPreExp i (Lambda x pe) = unwords ["\\", nameBase x, "->", pprintPreExp (i + 1) pe]
pprintPreExp i (Case e ms) =
  unwords
    [ "case",
      pprint e,
      "of",
      concat [unwords [indent i, pprint p, "->", indent (i + 1), pprintPreExp (i + 2) pe] | (p, pe) <- ms]
    ]
pprintPreExp i (If e pe1 pe2) =
  unwords
    [ "if",
      pprint e,
      indent i ++ "then",
      indent (i + 1) ++ pprintPreExp (i + 2) pe1,
      indent i ++ "else",
      indent (i + 1) ++ pprintPreExp (i + 2) pe2
    ]
pprintPreExp i (Exp e pe) =
  unwords
    [ "(" ++ pprint e ++ ")",
      "&&&",
      indent i ++ pprintPreExp (i + 1) pe
    ]
pprintPreExp i (AutoPreExp es st pe) =
  let es' = es <> kept st
   in if null es'
        then pprintPreExp i pe
        else
          unwords
            [ "(" ++ List.intercalate " &&& " ["(" ++ pprint e ++ ")" | e <- es'] ++ ")",
              "&&&",
              indent i ++ pprintPreExp (i + 1) pe
            ]
pprintPreExp i (TrivialPreExp) = "trivial"

pprintPreDec :: PreDec -> String
pprintPreDec (PreDec x t pe) =
  concat
    [ indent 0 ++ unwords [nameBase x, "::", pprint t],
      indent 0 ++ unwords [nameBase x, "="],
      indent 1 ++ pprintPreExp 2 pe
    ]
