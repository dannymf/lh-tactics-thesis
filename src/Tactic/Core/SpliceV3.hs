{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant pure" #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Core.SpliceV3 where

import Prelude hiding (exp)
import Data.Maybe
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
import Text.Printf

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
    go :: [Instr] -> Splice PreExp
    go [] = pure TrivialPreExp
    go (Intro {name} : instrs) = do
      name <- pure $ mkName name
      env <- get
      types <- gets def_argTypes
      def_type <- gets def_type
      i <- gets arg_i
      env <- get
      case types `index` i of
        Just type_ -> do modify $ introArg name type_
        Nothing -> fail $ "Cannot intro " ++ show name ++ " at index  " ++ show i ++ " in def_type " ++ pprint def_type
      Lambda name <$> go instrs
    go (Destruct {name, intros, flags} : instrs) = 
      destruct name intros flags instrs
    go (Induct {name, intros, flags} : instrs) = 
      induct name intros flags instrs
    go (Assert {exp, requires} : instrs) = do
      env <- get
      inScope <- lift $ all isJust <$> mapM (\x -> inferType (nameToExp $ mkName x) env) requires
      if inScope
        then If exp <$> go instrs <*> pure TrivialPreExp
        else go instrs
    go (Dismiss {exp, requires} : instrs) = do
      env <- get
      inScope <- lift $ all isJust <$> mapM (\x -> inferType (nameToExp $ mkName x) env) requires
      if inScope
        then flip (If exp) <$> go instrs <*> pure TrivialPreExp
        else go instrs
    go (Use {exp, requires} : instrs) = do
      env <- get
      inScope <- lift $ all isJust <$> mapM (\x -> inferType (nameToExp $ mkName x) env) requires
      if inScope
        then Exp exp <$> go instrs
        else go instrs
    go (Cond {exp, requires} : instrs) = do
      env <- get
      inScope <- lift $ all isJust <$> mapM (\x -> inferType (nameToExp $ mkName x) env) requires
      if inScope
        then do
          pe <- go instrs
          pure $ If exp pe pe
        else go instrs
    go (Trivial : instrs) =
      go instrs
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
          $ genNeutralsV3 proof depth
      AutoPreExp es initPruneAutoState <$> go instrs
    go _ = error "unsupported case"

    destruct :: String -> Maybe [[String]] -> [String] -> [Instr] -> Splice PreExp
    destruct name intros flags instrs = do
      name <- pure $ mkName name
      env <- get
      mb_type <- get >>= lift . inferType (VarE name)
      case mb_type of
        Just (ConT dtName) -> destructDt name intros flags dtName instrs 
        Just (AppT (ConT dtName) _) -> destructDt name intros flags dtName instrs
        Just type_ -> fail $ "Cannot destruct " ++ show name ++ " of non-datatype type " ++ show type_
        Nothing -> go instrs -- skip this instruction, since target not in scope
    
    destructDt :: Name -> Maybe [[String]] -> [String] -> Name -> [Instr] -> Splice PreExp
    destructDt name intros flags dtName instrs = local do
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
    induct :: String -> Maybe [[String]] -> [String] -> [Instr] -> Splice PreExp
    induct name intros flags instrs = do
      name <- pure $ mkName name
      env <- get
      mb_type <- get >>= \env -> lift $ inferType (VarE name) env
      case mb_type of
        Just (ConT dtName) -> inductDt name intros flags dtName instrs
        Just (AppT (ConT dtName) _) -> inductDt name intros flags dtName instrs
        Just type_ -> fail $ "Cannot induct " ++ show name ++ " of non-datatype type " ++ show type_
        Nothing -> go instrs -- skip this instruction, since target not in scope
    
    inductDt :: Name -> Maybe [[String]] -> [String] -> Name -> [Instr] -> Splice PreExp
    inductDt name intros flags dtName instrs = local do
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


type Goal = Type

type Gas = Int

type Splice a = StateT Environment Q a

type TypeSubs = Map.Map Type Type

genNeutralsV3 :: Goal -> Gas -> Splice [Exp]
genNeutralsV3 goal 0 = pure []
genNeutralsV3 goal gas = do
  let (alphas, beta) = flattenType goal
  recursions <- genRecursions goal gas
  debugSplice $! printf "INIT CALL: genNeutralsV3: alphas=%s | beta=%s | recursions=%s" (pprint alphas) (pprint beta) (pprint recursions) 
  genNeutralsAux beta recursions gas

genNeutralsAux :: Goal -> [Exp] -> Gas -> Splice [Exp]
genNeutralsAux goal recursions 0 = pure []
genNeutralsAux goal recursions gas = do
  vars <- Map.toList <$> gets ctx
  let f :: [Exp] -> (Exp, Type) -> Splice [Exp]
      f es (e, alpha) =
        (es <>)
          <$> 
          let (_, beta) = flattenType alpha in 
                if compareTypesPoly' beta goal
                    then do
                      debugSplice $! "DEBUG TYP: genNeutralsV3: alpha= " ++ pprint beta
                      -- MAKE THIS AUX ALSO BC OTHERWISE IT JUST REPEATEDLY RECURSES ON THE FUNCTION ARGUMENTS TOO
                      exps <- genNeutralsV3' e alpha recursions (gas - 1)
                      pure exps
                    else pure []
  es <- (<>) <$> foldM f [] vars <*> pure recursions
  debugSplice $! "DEBUG: genNeutralsV3: goal= " ++ show goal ++ " | es= " ++ show es
  pure es

genNeutralsV3' :: Exp -> Type -> [Exp] -> Gas -> Splice [Exp]
genNeutralsV3' e type_ recursions 0 = pure []
genNeutralsV3' e type_ recursions gas = do
  debugSplice $! "DEBUG: genNeutralsPRIME: e= " ++ pprint e ++ " | type= " ++ pprint type_
  ctx <- gets ctx
  let (alphas, beta) = flattenType type_
  es <-
    if List.null alphas
      then pure [e]
      else do
        argss <- fanout <$> traverse (genNeutralsAux type_ (gas - 1) ctx) alphas
        let es = foldl AppE e <$> argss
        pure es
  debugSplice $! "DEBUG: genNeutralsPRIME: e= " ++ pprint e ++ " | type= " ++ pprint type_ ++ " | es= " ++ show (pprint <$> es)
  pure es

-- IF YOU HAVE A LIST A AND TYPE VARIABLE, THEN YOU GENERATE THE TERM LIST CONT TYPE

-- | generates any expressions directly from context (no applications) that have goal type
genAtomsFromCtx :: Gas -> Ctx -> Type -> Splice [Exp]
genAtomsFromCtx 0 ctx type_ = pure []
genAtomsFromCtx gas ctx type_ = do
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
          terms <- genAtomsFromCtx (gas-1) ctx ty
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
      ctx <- gets ctx
      debugSplice $! printf "DBG genRecusrions: def_type=%s" (pprint rho)
      let (alphas, beta) = flattenType rho
      -- if compareTypesPoly' beta goal
      --   then do
      debugSplice $! "genRecursions DEBUG TYP: genNeutralsV2: alpha= " ++ pprint rho
      if List.null alphas
        then fail "impossible: cannot recurse with 0 arguments"
        else do
          argss <-
            fanout
              <$> traverse
                ( \(arg_i, alpha) -> do
                    gets args_rec_ctx
                      >>= ( \case
                              Just rec_ctx -> genAtomsFromCtx 3 rec_ctx alpha -- gen only vars from ctx
                              Nothing -> genAtomsFromCtx 3 ctx alpha
                          )
                        . Map.lookup arg_i -- gen any neutral
                )
                (zip [0 .. length alphas] alphas)
          -- debugSplice $! "genRecursions.argss: " ++ pprint (foldl AppE r <$> argss)
          pure $ foldl AppE r <$> argss
        -- else pure []
    False -> pure []

canRecurse :: Splice Bool
canRecurse = not . Map.null <$> gets args_rec_ctx

contains' :: Type -> Type -> Bool
contains' t1 t2 = case (t1, t2) of
  (VarT _, ConT _) -> False
  (ConT _, VarT _) -> False
  (ConT a, ConT b) | nameBase a == nameBase b -> True
  (VarT a, VarT b) -> True
  (AppT a b, VarT c) -> contains' a (VarT c) || contains' b (VarT c)
  (VarT c, AppT _ _) -> False
  _ -> False

compareTypesPoly' :: Type -> Type -> Bool
compareTypesPoly' t1 t2 = case (t1, t2) of
  (ConT n1, ConT n2) -> nameBase n1 == nameBase n2
  (VarT a, VarT b) -> True -- this rule is likely wrong
  (a, VarT b) | a /= ConT ''Proof && not (a `contains'` VarT b) -> True
  -- (VarT a, VarT b) -> True
  -- (VarT a, ConT b) | b /= ''Proof -> True
  (AppT (AppT ArrowT a) b, AppT (AppT ArrowT c) d) -> True
    -- compareTypesPoly' a c && compareTypesPoly' b d
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