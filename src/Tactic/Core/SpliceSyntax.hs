{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant pure" #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Core.SpliceSyntax where

import Data.Maybe
import Control.Monad
import Control.Monad.Trans as Trans
import Control.Monad.Trans.State as State
import Data.Char as Char
import Data.List as List
import qualified Data.List as List
import qualified Data.Map as Map
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

type Splice a = StateT Environment Q a

debugSplice :: String -> Splice ()
debugSplice = lift . debugQ

-- restricts to local state
local :: Splice a -> Splice a
local m = do
  st <- get
  lift $ evalStateT m st

freshName :: String -> Splice Name
freshName str = do
  env <- get
  let i = var_i env
  let name = mkName $ str ++ "_" ++ show i
  put $ env {var_i = i + 1}
  pure name

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
                    modify $ flip (foldl (\env (e, type_) -> insertCtx e type_ env)) (fmap (\(n, t) -> (VarE n, t)) vars)
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
                    gets def_argNames >>= (\case
                      Just arg_i -> do
                        modify $ \env -> env {args_rec_ctx = Map.insert arg_i (Map.fromList . fmap (\(n, t) -> (VarE n, t)) $ vars) (args_rec_ctx env)}
                      Nothing -> do
                        -- TODO: dont need this anymore, since can induct on non-arguments: fail $ "Cannot find argument index of argument " ++ show name
                        -- ! however, this could potentially cause problems where it's possible to auto your way into infinite recursion, right?
                        return ()) . List.elemIndex name
                    -- adds constructor's introduced terms to environment
                    modify $ flip (foldl (flip (uncurry insertCtx))) ((\(n, t) -> (VarE n, t)) <$> vars)
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
    go (Assert {exp, requires} : instrs) = do
      env <- get
      inScope <- lift $ all isJust <$> mapM (\x -> inferType (nameToExp $ mkName x) env) requires
      if inScope then
        If exp <$> go instrs <*> pure TrivialPreExp
      else
        go instrs
    go (Dismiss {exp, requires} : instrs) = do
      env <- get
      inScope <- lift $ all isJust <$> mapM (\x -> inferType (nameToExp $ mkName x) env) requires
      if inScope then
        flip (If exp) <$> go instrs <*> pure TrivialPreExp
      else
        go instrs
    go (Use {exp, requires} : instrs) = do
      env <- get
      inScope <- lift $ all isJust <$> mapM (\x -> inferType (nameToExp $ mkName x) env) requires
      if inScope then
        Exp exp <$> go instrs
      else
        go instrs
    go (Cond {exp, requires} : instrs) = do
      env <- get
      inScope <- lift $ all isJust <$> mapM (\x -> inferType (nameToExp $ mkName x) env) requires
      if inScope then do
        pe <- go instrs
        pure $ If exp pe pe
      else
        go instrs
    go (Trivial : instrs) =
      go instrs
    go (Refine {string, requires} : instrs) = do
      -- env <- get
      -- refinement <- interpretRefinement string
      error "unimplemented: refine"
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
          $ genNeutrals (Just proof) depth
      AutoPreExp es initPruneAutoState <$> go instrs
    go _ = error "unsupported case"

interpretRefinement :: String -> Splice ([Type], [Exp] -> Exp)
interpretRefinement string = undefined

mapWithIndex :: (Int -> a -> b) -> [a] -> [b]
mapWithIndex f xs = go 0 xs
  where
    go i [] = []
    go i (x : xs) = f i x : go (i + 1) xs

-- for better error messages
indexIntros :: Maybe [[String]] -> Int -> Maybe [String]
indexIntros mb_intros i = f <$> mb_intros
  where
    f intros = case index intros i of
      Just intro -> intro
      Nothing -> error $ "The intros " ++ show intros ++ "expected at least " ++ show i ++ " cases"

spliceDec :: [Instr] -> Splice PreDec
spliceDec instrs = do
  env <- get
  PreDec (def_name env) (def_type env) <$> spliceExp instrs

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

type Goal = Maybe Type

type Gas = Int

genNeutrals :: Goal -> Gas -> Splice [Exp]
genNeutrals goal 0 = pure []
genNeutrals goal gas = do
  vars <- Map.toList <$> gets ctx
  let f :: [Exp] -> (Exp, Type) -> Splice [Exp]
      f es (e, alpha) =
        (es <>)
          <$> let (_, beta) = flattenType alpha
               in if matchesGoal beta goal
                    then genNeutrals' e alpha gas
                    else pure []
  es <- (<>) <$> foldM f [] vars <*> genRecursions goal gas
  pure es

genNeutrals' :: Exp -> Type -> Gas -> StateT Environment Q [Exp]
genNeutrals' e type_ gas = do
  let (alphas, beta) = flattenType type_
  es <-
    if List.null alphas
      then pure [e]
      else do
        argss <- fanout <$> traverse (\alpha -> genNeutrals (Just alpha) (gas - 1)) alphas
        let es = foldl AppE e <$> argss
        pure es
  -- debugSplice $! "genNeutrals' (" ++ pprint e ++ ") (" ++ pprint type_ ++ ") " ++ show gas ++ " = " ++ show (pprint <$> es)
  pure es

-- | generates any expressions directly from context (no applications) that have goal type
genAtomsFromCtx :: Ctx -> Type -> Splice [Exp]
genAtomsFromCtx ctx type_ = do
  let f :: [Exp] -> (Exp, Type) -> Splice [Exp]
      f es (e, alpha) =
        (es <>) <$> if alpha `compareTypes` type_ then pure [e] else pure []
  es <- foldM f [] (Map.toList ctx)
  pure es

genRecursions :: Goal -> Int -> Splice [Exp]
genRecursions goal gas = do
  canRecurse >>= \case
    True -> do
      r <- VarE <$> gets def_name
      rho <- gets def_type
      let (alphas, beta) = flattenType rho
      if matchesGoal beta goal
        then do
          if List.null alphas
            then fail "impossible: cannot recurse with 0 arguments"
            else do
              argss <-
                fanout
                  <$> traverse
                    ( \(arg_i, alpha) -> do
                        gets args_rec_ctx >>= (\case
                          Just rec_ctx -> genAtomsFromCtx rec_ctx alpha -- gen only vars from ctx
                          Nothing -> genNeutrals (Just alpha) (gas - 1)) . Map.lookup arg_i -- gen any neutral
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