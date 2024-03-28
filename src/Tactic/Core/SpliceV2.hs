{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant pure" #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Core.SpliceV2 where

import Control.Monad
import Control.Monad.Trans as Trans
import Control.Monad.Trans.State as State
import Data.Bifunctor
import Data.Char as Char
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Syntax hiding (lift)
import Proof
import Tactic.Core.Debug
import Tactic.Core.PreSyntax
import Tactic.Core.Syntax
import Tactic.Core.Utility

-- JUST DO GENNEUTRALS FOR THE DESIRED TYPE-- LIKE LIST A???

-- restricts to local state
local :: Splice a -> Splice a
local m = do
  st <- get
  lift $ evalStateT m st

spliceExp :: [Instr] -> Splice PreExp
spliceExp instrs =
  if not (null instrs)
    then case last instrs of
      Trivial -> go instrs
      Auto _ _ -> go instrs
      _ -> go (instrs ++ [Auto {hints = defaultAutoHints, depth = defaultAutoDepth}])
    else go instrs
  where
    go (Destruct {name, intros, flags} : instrs) = do
      name <- pure $ mkName name
      env <- get
      mb_type <- get >>= lift . inferType (VarE name)
      case mb_type of
        (Just type_@(ConT dtName)) -> local do
          -- remove destructed target from environment
          unless ("remember" `elem` flags) $ do
            modify $ deleteCtx (VarE name)
          -- get datatype info
          dtInfo <- lift $ reifyDatatype dtName
          -- gen matches
          let dtConInfos = datatypeCons dtInfo

          let matches :: [Splice (Pat, PreExp)]
              matches =
                ( \i conInfo -> local do
                    -- collects newly bound variables with types, generates match's pattern
                    (vars, pat) <- getConVarsPat conInfo (indexIntros intros i)
                    -- adds constructor's introduced terms to environment
                    modify $ flip (foldl (\env (e, type_) -> insertCtx e type_ env)) (fmap (first VarE) vars)
                    -- body
                    expr <- go instrs
                    -- gen match
                    pure (pat, expr)
                )
                  `mapWithIndex` dtConInfos
          -- generate case
          ms <- sequence matches
          --
          pure $ Case (VarE name) ms
        Just type_ -> fail $ "Cannot destruct " ++ show name ++ " of non-datatype type " ++ show type_
        Nothing -> go instrs -- skip this instruction, since target not in scope
    go (Induct {name, intros, flags} : instrs) = do
      name <- pure $ mkName name
      env <- get
      mb_type <- get >>= \env -> lift $ inferType (VarE name) env

      case mb_type of
        Just type_@(ConT dtName) -> local do
          -- remove inducted target from environment
          unless ("remember" `elem` flags) $ do
            modify $ deleteCtx (VarE name)
          -- get datatype info
          dtInfo <- lift $ reifyDatatype dtName
          -- gen matches
          let dtConInfos = datatypeCons dtInfo
          let matches :: [Splice (Pat, PreExp)]
              matches =
                ( \i conInfo -> local do
                    -- collects newly bound variables with types, generates match's pattern
                    (vars, pat) <- getConVarsPat conInfo (indexIntros intros i)
                    -- add constructor's variables to `args_rec_ctx` at `name`
                    gets def_argNames
                      >>= ( \case
                              Just arg_i -> do
                                modify $ \env -> env {args_rec_ctx = Map.insert arg_i (Map.fromList . fmap (first VarE) $ vars) (args_rec_ctx env)}
                              Nothing -> do
                                -- TODO: dont need this anymore, since can induct on non-arguments: fail $ "Cannot find argument index of argument " ++ show name
                                -- ! however, this could potentially cause problems where it's possible to auto your way into infinite recursion, right?
                                return ()
                          )
                        . List.elemIndex name
                    -- adds constructor's introduced terms to environment
                    modify $ flip (foldl (flip (uncurry insertCtx))) (first VarE <$> vars)
                    --
                    expr <- go instrs
                    -- gen match
                    pure (pat, expr)
                )
                  `mapWithIndex` dtConInfos
          -- generate case
          ms <- sequence matches
          --
          pure $ Case (VarE name) ms
        Just (AppT (ConT a) (ConT b)) -> local do
          -- remove inducted target from environment
          unless ("remember" `elem` flags) $ do
            modify $ deleteCtx (VarE name)
          -- get datatype info
          dtInfo <- lift $ reifyDatatype a
          -- gen matches
          let dtConInfos = datatypeCons dtInfo
          let matches :: [Splice (Pat, PreExp)]
              matches =
                ( \i conInfo -> local do
                    -- collects newly bound variables with types, generates match's pattern
                    (vars, pat) <- getConVarsPat conInfo (indexIntros intros i)
                    -- add constructor's variables to `args_rec_ctx` at `name`
                    gets def_argNames
                      >>= ( \case
                              Just arg_i -> do
                                modify $ \env -> env {args_rec_ctx = Map.insert arg_i (Map.fromList . fmap (first VarE) $ vars) (args_rec_ctx env)}
                              Nothing -> do
                                -- TODO: dont need this anymore, since can induct on non-arguments: fail $ "Cannot find argument index of argument " ++ show name
                                -- ! however, this could potentially cause problems where it's possible to auto your way into infinite recursion, right?
                                return ()
                          )
                        . List.elemIndex name
                    -- adds constructor's introduced terms to environment
                    modify $ flip (foldl (flip (uncurry insertCtx))) (first VarE <$> vars)
                    --
                    expr <- go instrs
                    -- gen match
                    pure (pat, expr)
                )
                  `mapWithIndex` dtConInfos
          -- generate case
          ms <- sequence matches
          --
          pure $ Case (VarE name) ms
        Just type_ -> fail $ "Cannot induct " ++ show name ++ " of non-datatype type " ++ show type_
        Nothing -> go instrs -- skip this instruction, since target not in scope
    go (Auto {hints, depth} : instrs) = do
      env <- get
      -- ctx' <- lift $ Map.fromList <$> mapM (\x -> (x,) <$> inferType x env) hints
      let typings =
            mapM
              ( \x -> do
                  mb_type <- inferType x env
                  case mb_type of
                    Just type_ -> pure [(x, type_)]
                    Nothing -> pure []
              )
              hints
      ctx' <- lift $ Map.fromList <$> (concat <$> typings)
      proof <- lift [t|Proof|]
      es <-
        withStateT
          (\env -> env {ctx = Map.union ctx' (ctx env)})
          $ genNeutralsV2 (Just proof) depth
      AutoPreExp es initPruneAutoState <$> go instrs
    go _ = error "unsupported case"

type Goal = Maybe Type

type Gas = Int

type Splice a = StateT Environment Q a

type TypeSubs = Map.Map Type Type

insertSubs :: [(Type, Type)] -> Environment -> Environment
insertSubs subs env =
  List.foldl' (\subs (t1, t2) -> env {tyvar_mappings = Map.insert t1 t2 $ tyvar_mappings env}) env subs

deleteSubs :: [Type] -> Environment -> Environment
deleteSubs ts env =
  List.foldl' (\subs t -> env {tyvar_mappings = Map.delete t $ tyvar_mappings env}) env ts

genNeutralsV2 :: Goal -> Gas -> Splice [Exp]
genNeutralsV2 goal 0 = pure []
genNeutralsV2 goal gas = do
  vars <- Map.toList <$> gets ctx
  let f :: [Exp] -> (Exp, Type) -> Splice [Exp]
      f es (e, alpha) =
        (es <>)
          <$> let (_, beta) = flattenType alpha
                  (boo, subs) = maybe (False, []) (\goal' -> (compareTypesPoly' beta goal', [])) goal
               in if boo
                    then do
                      debugSplice $! "DEBUG TYP: genNeutralsV2: alpha= " ++ pprint alpha
                      modify $ insertSubs subs
                      exps <- genNeutralsV2' e alpha gas
                      modify $ deleteSubs (fst <$> subs)
                      pure exps
                    else pure []
  es <- (<>) <$> foldM f [] vars <*> genRecursions goal gas
  debugSplice $! "DEBUG: genNeutralsV2: goal= " ++ show goal ++ " | es= " ++ show es
  pure es

genNeutralsV2' :: Exp -> Type -> Gas -> StateT Environment Q [Exp]
genNeutralsV2' e type_ gas = do
  let (alphas, beta) = flattenType type_
  es <-
    if List.null alphas
      then pure [e]
      else do
        argss <- fanout <$> traverse (\alpha -> genNeutralsV2 (Just alpha) (gas - 1)) alphas
        let es = foldl AppE e <$> argss
        pure es
  debugSplice $! "DEBUG: genNeutralsPRIME: e= " ++ pprint e ++ " | type= " ++ pprint type_ ++ " | es= " ++ show (pprint <$> es)
  pure es

-- IF YOU HAVE A LIST A AND TYPE VARIABLE, THEN YOU GENERATE THE TERM LIST CONT TYPE

-- | generates any expressions directly from context (no applications) that have goal type
genAtomsFromCtx :: Gas -> Ctx -> TypeSubs -> Type -> Splice [Exp]
genAtomsFromCtx 0 ctx subs type_ = pure []
genAtomsFromCtx gas ctx subs type_ = do
  let f :: [Exp] -> (Exp, Type) -> Splice [Exp]
      f es (e, alpha) = do
        debugSplice $! "DEBUG: compareTypesPoly: COMPARED alpha:" ++ show alpha ++ " and type_:" ++ show type_ ++ " | result: " ++ show (alpha `compareTypesPoly'` type_)
        (es <>) <$> if alpha `compareTypesPoly'` type_ then pure [e] else pure []
  es <- foldM f [] (Map.toList ctx)
  debugSplice $! "DEBUG: genAtomsFromCtx: type= " ++ pprint type_ ++ " | es= " ++ show (pprint <$> es)
  pure es
  
  
  
--   genAtomsFromCtx :: Gas -> Ctx -> TypeSubs -> Type -> Splice [Exp]
-- genAtomsFromCtx 0 ctx subs type_ = 
--   pure []
-- genAtomsFromCtx gas ctx subs type_ = do
--   -- Applications!
--   es <- foldM f [] (Map.toList ctx)
--   pure es
--   where
--     g :: [Exp] -> (Exp, Type) -> Splice [Exp]
--     g es (_, ty) =
--       case ty of
--         AppT (ConT dtName) (VarT x) -> do
--           dtInfo <- lift $ reifyDatatype dtName
--           let dtConInfos = datatypeCons dtInfo
--           let conNames = constructorName <$> dtConInfos
--           let listConFields = constructorFields <$> dtConInfos
--           debugSplice $! "genAtomsFromCtx.listConFields: " ++ pprint listConFields
--           expsss :: [[[Exp]]] <- zipWithM (genApps (gas - 1) ctx subs) conNames listConFields
--           debugSplice $! "genAtomsFromCtx.expsss: " ++ pprint expsss
--           pure []
        
--         _ -> error "oops"

--     f :: [Exp] -> (Exp, Type) -> Splice [Exp]
--     f es (e, alpha) = g es (e, alpha)
      -- case alpha of
      --   AppT (ConT c) (VarT x) -> g es (e, alpha)
      --   _ -> (es <>) <$> if mReplace subs alpha `compareTypes` type_ then pure [e] else pure []

-- generate all neutrals for a constructor and its fields
genApps :: Gas -> Ctx -> TypeSubs -> Name -> [Type] -> Splice [[Exp]]
genApps 0 ctx typeSubs conName conFields = pure []
genApps gas ctx typeSubs conName conFields = do
  -- generate all the expressions that match the types from the context
  -- once you got all the expressions, then you can just put that list of
  -- expressions after the conE name. So basically you got a list of lists of
  -- lists of expressions so that for each list in your list of lists of lists
  -- you can combine that with the constructor
  conFieldExps <-
    foldM
      ( \expss ty -> do
          debugSplice $! "genApps.foldM: looking for..." ++ pprint ty
          terms <- genAtomsFromCtx (gas-1) ctx typeSubs ty
          when (List.null terms) $ debugSplice $! "Oh no!!! Couldn't find any terms matching type " ++ pprint ty
          pure $ expss ++ [terms]
      )
      []
      conFields
  debugSplice $! "genApps.conFieldExps: " ++ "(conName: " ++ pprint conName ++ ") " ++ pprint conFieldExps
  pure conFieldExps

genRecursions :: Goal -> Int -> Splice [Exp]
genRecursions goal gas = do
  canRecurse >>= \case
    True -> do
      r <- VarE <$> gets def_name
      rho <- gets def_type
      let (alphas, beta) = flattenType rho
      if maybe False (compareTypesPoly' beta) goal
        then do
          debugSplice $! "genRecursions DEBUG TYP: genNeutralsV2: alpha= " ++ pprint rho
          if List.null alphas
            then fail "impossible: cannot recurse with 0 arguments"
            else do
              subs <- gets tyvar_mappings
              argss <-
                fanout
                  <$> traverse
                    ( \(arg_i, alpha) -> do
                        gets args_rec_ctx
                          >>= ( \case
                                  Just rec_ctx -> genAtomsFromCtx 3 rec_ctx subs alpha -- gen only vars from ctx
                                  Nothing -> genNeutralsV2 (Just alpha) (gas - 1)
                              )
                            . Map.lookup arg_i -- gen any neutral
                    )
                    (zip [0 .. length alphas] alphas)
              -- debugSplice $! "genRecursions.argss: " ++ pprint (foldl AppE r <$> argss)
              pure $ foldl AppE r <$> argss
        else pure []
    False -> pure []

canRecurse :: Splice Bool
canRecurse = not . Map.null <$> gets args_rec_ctx

matchesGoal :: Type -> Goal -> Bool
matchesGoal type_ = maybe True (`compareTypes` type_)

matchesGoalPoly :: Type -> Goal -> (Bool, [(Type, Type)])
matchesGoalPoly type_ = maybe (True, []) (`compareTypesPoly` type_)

compareTypesPoly :: Type -> Type -> (Bool, [(Type, Type)])
compareTypesPoly t1 t2 = case (t1, t2) of
  (ConT n1, ConT n2) -> (nameBase n1 == nameBase n2, [])
  (VarT a, t2) -> (True, [(VarT a, t2)])
  (AppT a1 b1, AppT a2 b2) | a1 == a2 -> compareTypesPoly b1 b2
  _ -> (False, [])
  --  t1, t2 | t1 == t2

compareTypesPoly' :: Type -> Type -> Bool
compareTypesPoly' t1 t2 = case (t1, t2) of
  (ConT n1, ConT n2) -> nameBase n1 == nameBase n2
  (VarT a, _) -> True
  -- (VarT a, VarT b) -> True
  -- (VarT a, ConT b) | b /= ''Proof -> True
  (AppT a1 b1, AppT a2 b2) -> compareTypesPoly' a1 a2 && compareTypesPoly' b1 b2
  -- AppT List \ int -> bool
  _ -> False

-- error $ "compare types: unsupported comparison between " ++ show t1 ++ " and " ++ show t2

getConVarsPat :: ConstructorInfo -> Maybe [String] -> Splice ([(Name, Type)], Pat)
getConVarsPat conInfo mb_intro = do
  let conName = constructorName conInfo
  let conFields = constructorFields conInfo
  names <-
    case mb_intro of
      Just intro -> pure $ mkName <$> intro
      Nothing -> mapM typeToTermName conFields
  let vars = (\(name, type_) -> (name, type_)) <$> zip names conFields
  let pat = ConP conName $ VarP <$> names
  pure (vars, pat)

typeToTermName :: Type -> Splice Name
typeToTermName type_ =
  case type_ of
    ConT name -> case nameBase name of
      (c : s) -> freshName (Char.toLower c : s)
      [] -> error "empty"
    _ -> freshName "x"

-- for better error messages
indexIntros :: Maybe [[String]] -> Int -> Maybe [String]
indexIntros mb_intros i = f <$> mb_intros
  where
    f intros = case index intros i of
      Just intro -> intro
      Nothing -> error $ "The intros " ++ show intros ++ "expected at least " ++ show i ++ " cases"

freshName :: String -> Splice Name
freshName str = do
  env <- get
  let i = var_i env
  let name = mkName $ str ++ "_" ++ show i
  put $ env {var_i = i + 1}
  pure name

mapWithIndex :: (Int -> a -> b) -> [a] -> [b]
mapWithIndex f xs = go 0 xs
  where
    go i [] = []
    go i (x : xs) = f i x : go (i + 1) xs

mReplace :: Ord a => Map.Map a a -> a -> a
mReplace map ty = fromMaybe ty (Map.lookup ty map)

debugSplice :: String -> Splice ()
debugSplice = lift . debugQ