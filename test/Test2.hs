{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC "-ddump-splices" #-}

{-@ LIQUID "--compile-spec" @-}

module Test2 where

import Data.Serialize
import Language.Haskell.TH.Ppr
import Proof
import Tactic.Core.PreSyntax
import Tactic.Core.Quote
import Tactic.Core.SplicePreSyntax

data A = A Int

data B = B Int

data C = C Int

data D = D Int

data E = E Int

{-@ reflect f1 @-}
f1 :: A -> B
f1 (A x) = B x

{-@ reflect f2 @-}
f2 :: B -> C
f2 (B x) = C x

{-@ reflect f3 @-}
f3 :: C -> D
f3 (C x) = D x

{-@ reflect f4 @-}
f4 :: D -> E
f4 (D x) = E x

{-@ reflect lemB @-}
lemB :: B -> Proof 
lemB (B x) = trivial

{-@ reflect lemC @-}
lemC :: C -> Proof 
lemC (C x) = trivial

{-@ reflect lemD @-}
lemD :: D -> Proof 
lemD (D x) = trivial

{-@ reflect lemE @-}
lemE :: E -> Proof 
lemE (E x) = trivial

return [] 

-- [tactic|
-- test :: A -> Proof
-- test a = auto [f1, f2, f3, f4, lemE] 6
-- |]

-- | ]
main :: IO ()
main = do
  -- print _tactic_encoding_test1
  -- putStrLn ""
  -- let preDec = decode_ _tactic_encoding_test1 :: PreDec
  -- print preDec
  -- putStrLn ""
  -- let decs = splicePreDec preDec
  -- putStrLn $ pprint decs
  return ()
