{-# Language TemplateHaskell #-}
{-# Language QuasiQuotes #-}

{-# OPTIONS_GHC "-ddump-splices" #-}

{-@ LIQUID "--compile-spec" @-}

module Test1 where

import Language.Haskell.TH.Ppr
import Tactic.Core.Quote
import Proof
import Tactic.Core.PreSyntax
import Tactic.Core.SplicePreSyntax
import Data.Serialize

data A = A1 Int | A2 A
data B = B1 Proof | B2

test = (\x -> trivial) :: Bool -> Proof

f :: Proof -> Proof
f x = x

return []

-- [tactic|
-- test1 :: A -> A -> Proof
-- test1 a1 a2 =
-- |]

[tactic|
test1 :: B -> Proof
test1 b =
  induct b as [pf/];
  use {f (f pf)} requires [pf]
|]


main = do
  print _tactic_encoding_test1
  putStrLn ""
  let preDec = decode_ _tactic_encoding_test1 :: PreDec
  print preDec
  putStrLn ""
  let decs = splicePreDec preDec
  putStrLn $ pprint decs

