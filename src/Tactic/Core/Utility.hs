{-# LANGUAGE TemplateHaskell #-}

module Tactic.Core.Utility where

{-@ LIQUID "--compile-spec" @-}

import Data.Char as Char
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax

flattenType :: Type -> ([Type], Type)
flattenType (AppT (AppT ArrowT alpha) beta) =
  let (alphas, delta) = flattenType beta
   in (alpha : alphas, delta)
flattenType (AppT (AppT (AppT MulArrowT (PromotedT n)) alpha) beta) =
  -- TODO: only works when `n` is `GHC.Types.One`
  let (alphas, delta) = flattenType beta
   in (alpha : alphas, delta)
flattenType alpha = ([], alpha)

-- unflattenType :: ([Type], Type) -> Type
-- unflattenType [] beta = beta
-- unflattenType (alpha : alphas) beta = AppT (AppT ArrowT alpha) (unflattenType alphas beta)

-- because normal equality treats the types `ConT N` and `ConT Path.To.Module.N` as different, even if they are the same... how to fix this???
compareTypes :: Type -> Type -> Bool
compareTypes (ConT n1) (ConT n2) = nameBase n1 == nameBase n2
compareTypes (AppT a1 b1) (AppT a2 b2) = compareTypes a1 a2 && compareTypes b1 b2
compareTypes t1 t2 = t1 == t2

index :: [a] -> Int -> Maybe a
index [] _ = Nothing
index (x : xs) 0 = Just x
index (_ : xs) i = index xs (i - 1)

-- | for each list of the output, the ith element is from the ith list of the input.
-- all lists must be of the same length.
-- example: [ [x1, x2], [y1, y2] ] ==> [ [x1, y1], [x1, y2], [x2, y1], [x2, y2] ]
fanout :: [[a]] -> [[a]]
fanout [] = []
fanout (xs : []) = [[a] | a <- xs]
fanout (xs : xss) = [a' : xs' | a' <- xs, xs' <- fanout xss]

-- useMany [e1, e2, e3] == [|use e1 &&&& use e2 &&& use e3|]
useMany :: [Exp] -> Q Exp
useMany [] = [|trivial|]
useMany [e] = [|use $(pure e)|]
useMany (e : es) = [|use $(pure e) &&& $(useMany es)|]

conjunction :: [Exp] -> Q Exp
conjunction [] = [|trivial|]
conjunction [e] = pure e
conjunction (e : es) = [|$(pure e) &&& $(conjunction es)|]

conjunctionExp :: [Exp] -> Exp 
conjunctionExp [] = VarE (mkName "trivial")
conjunctionExp [e] = e 
conjunctionExp (e:es) = InfixE (Just e) (VarE (mkName "&&&")) (Just (conjunctionExp es))