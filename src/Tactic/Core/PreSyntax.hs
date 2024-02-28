{-# LANGUAGE BlockArguments #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Core.PreSyntax where

import Control.Monad.State
import qualified Data.List as List
import Data.Map as Map
import Data.Maybe
import Data.Serialize
import Language.Haskell.Meta.Parse
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Ppr (pprint)
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import System.IO.Unsafe (unsafePerformIO)
import Tactic.Core.Debug
import Prelude hiding (exp)
import Data.List (intercalate)

data PreExp
  = Lambda Name PreExp
  | Case Exp [(Pat, PreExp)]
  | If Exp PreExp PreExp
  | Exp Exp PreExp
  | AutoPreExp [Exp] PruneAutoState PreExp
  | TrivialPreExp
  deriving (Show)

data PruneAutoState = PruneAutoState
  { kept :: [Exp],
    pruned :: [Exp]
  }
  deriving (Show)

initPruneAutoState =
  PruneAutoState
    { kept = mempty,
      pruned = mempty
    }

data PreDec
  = PreDec Name Type PreExp
  deriving (Show)

-- instance Show PreExp where
--   show (Lambda x pe) = "(\\ " ++ pprint x ++ " " ++ show pe ++ ")"
--   show (Case arg ms) = "(case " ++ pprint arg ++ " of {" ++ List.intercalate "; " ((\(pat, expr) -> pprint pat ++ " -> " ++ show expr) <$> ms) ++ "})"
--   show (If e pe1 pe2) = "(if " ++ pprint e ++ " then " ++ show pe1 ++ " else " ++ show pe2 ++ ")"
--   show (Exp e pe) = "(" ++ pprint e ++ ") &&& " ++ show pe ++ ")"
--   show (AutoPreExp es _ pe) = "(Auto(" ++ List.intercalate " &&& " (pprint <$> es) ++ ") &&& " ++ show pe ++ ")"
--   show (TrivialPreExp) = "trivial"

-- instance Show PreDec where
--   show (PreDec x t pe) = "(" ++ pprint x ++ " :: " ++ pprint t ++ " := " ++ show pe ++ ")"

instance Serialize PreExp where
  encode (Lambda x pe) = concat ["#Lambda", encode x, encode pe]
  encode (Case arg ms) =
    concat
      [ "#Case",
        encode arg,
        "#BeginMatches",
        concat ((\(p, pe) -> concat ["#ItemMatch", encode p, "#,", encode pe]) <$> ms),
        "#EndMatches"
      ]
  encode (If e pe1 pe2) = concat ["#If", encode e, encode pe1, encode pe2]
  encode (Exp e pe) = concat ["#Exp", encode e, encode pe]
  encode (AutoPreExp es _ pe) =
    concat
      [ "#AutoPreExp",
        "#BeginAutoPreExps",
        concat ((\e -> "#ItemAutoExp" ++ encode e) <$> es),
        "#EndAutoPreExps",
        encode pe
      ]
  encode TrivialPreExp = "#TrivialPreExp"

  decode =
    decodeGroup "PreExp"
      [ decodeLabeled (decodeStringMaybe "#Lambda") $
          Lambda <$> decode <*> decode,
        decodeLabeled (decodeStringMaybe "#Case") $
          Case
            <$> decode
            <*> decodeList
              (decodeString "#BeginMatches")
              (decodeStringMaybe "#ItemMatch")
              ( do
                  p <- decode
                  decodeString "#,"
                  pe <- decode
                  pure (p, pe)
              )
              (decodeString "#EndMatches"),
        decodeLabeled (decodeStringMaybe "#If") $
          If <$> decode <*> decode <*> decode,
        decodeLabeled (decodeStringMaybe "#Exp") $
          Exp <$> decode <*> decode,
        decodeLabeled (decodeStringMaybe "#AutoPreExp") $
          AutoPreExp
            <$> decodeList
              (decodeString "#BeginAutoPreExps")
              (decodeStringMaybe "#ItemAutoExp")
              decode
              (decodeStringMaybe "#EndAutoPreExps")
            <*> pure initPruneAutoState
            <*> decode,
        decodeLabeled (decodeStringMaybe "#TrivialPreExp") $
          pure TrivialPreExp
      ]

instance Serialize PreDec where
  encode (PreDec x t e) = concat ["#Dec", encode x, encode t, encode e]
  decode =
    decodeGroup "PreDec"
      [ decodeLabeled (decodeStringMaybe "#Dec") $
          PreDec <$> decode <*> decode <*> decode
      ]

instance Serialize Type where
  encode t = concat ["#TypeBegin", pprint t, "#TypeEnd"]
  decode = do
    s <- decodeParen "#TypeBegin" "#TypeEnd"
    parseToDecode (parseType s)

instance Serialize Exp where
  encode e = concat ["#ExpBegin", pprint e, "#ExpEnd"]
  decode = do
    s <- decodeParen "#ExpBegin" "#ExpEnd"
    parseToDecode (parseExp s)

instance Serialize Pat where
  encode p = concat ["#PatBegin", pprint p, "#PatEnd"]
  decode = do
    s <- decodeParen "#PatBegin" "#PatEnd"
    parseToDecode (parsePat s)

instance Serialize Name where
  encode x = concat ["#NameBegin", show x, "#NameEnd"]
  decode = do
    x <- decodeParen "#NameBegin" "#NameEnd"
    pure $ mkName x
