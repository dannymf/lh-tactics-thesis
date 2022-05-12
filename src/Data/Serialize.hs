{-# LANGUAGE TupleSections #-}
{-@ LIQUID "--compile-spec" @-}

module Data.Serialize where

import Control.Monad.Except
import Control.Monad.State

type Decode a = StateT String (Except String) a

class Serialize a where
  encode :: a -> String
  decode :: Decode a

decode_ :: Serialize a => String -> a
decode_ s = case runExcept (runStateT decode s) of
  Left msg -> error msg
  Right (a, s) -> a

decodeString :: String -> Decode String
decodeString pre = do
  str <- get
  case unprefix pre str of
    Just (_, str') -> do
      put str'
      pure pre
    Nothing ->
      throwError $ "Decode error: expected " ++ show pre ++ " at " ++ show str

decodeStringMaybe :: String -> Decode (Maybe String)
decodeStringMaybe pre = do
  str <- get
  case unprefix pre str of
    Just (_, str') -> do
      put str'
      pure $ Just pre
    Nothing ->
      pure $ Nothing

decodeGroup :: String -> [Decode (Maybe a)] -> Decode a
decodeGroup label [] = do
  str <- get
  throwError $ "Decode error: expected group " ++ show label ++ " at " ++ show str
decodeGroup label (dec : decs) = do
  mb_a <- dec
  case mb_a of
    Just a -> pure a
    Nothing -> decodeGroup label decs

decodeLabeled :: Decode (Maybe a) -> Decode b -> Decode (Maybe b)
decodeLabeled decLabel decB = do
  mb_label <- decLabel
  case mb_label of
    Just _ -> pure <$> decB
    Nothing -> pure Nothing

decodeList :: Decode a -> Decode (Maybe b) -> Decode c -> Decode d -> Decode [c]
decodeList decStart decItem decC decEnd = do
  decStart
  cs <- go
  decEnd
  pure cs
  where
    go = do
      mb_item <- decItem
      case mb_item of
        Just _ -> (:) <$> decC <*> go
        Nothing -> pure []

-- decodeLabeledList :: Decode a -> Decode b -> Decode (Maybe c) -> Decode [b]
-- decodeLabeledList decItemLabel decB decEnd = do
--   mb_end <- decEnd
--   case mb_end of
--     Just _ -> pure []
--     Nothing -> do
--       decItemLabel
--       (:) <$> decB <*> decodeLabeledList decItemLabel decB decEnd

decodeParen :: String -> String -> Decode String
decodeParen lpar rpar = do
  str <- get
  case unparen lpar rpar str of
    Nothing -> throwError $ "Decode error: expected \"" ++ lpar ++ "..." ++ rpar ++ "\" at " ++ show str
    Just (s, str') -> do
      put str'
      pure s

unparen :: String -> String -> String -> Maybe (String, String)
unparen lpar rpar str1 =
  case unprefix lpar str1 of
    Nothing -> Nothing
    Just (_, str2) -> unsuffix rpar str2

unprefix :: String -> String -> Maybe (String, String)
unprefix pre str = (pre,) <$> go pre str
  where
    go "" str = Just str
    go pre "" = Nothing
    go (c1 : pre) (c2 : str)
      | c1 == c2 = go pre str
      | otherwise = Nothing

unsuffix :: String -> String -> Maybe (String, String)
unsuffix suf str = go suf str
  where
    go "" "" = Just ("", "")
    go suf "" = Nothing
    go suf (c : str) = case unprefix suf (c : str) of
      Nothing -> do
        (s, str') <- unsuffix suf str
        Just (c : s, str')
      Just (_, str') -> Just ("", str')

parseToDecode :: Either String a -> Decode a
parseToDecode (Left msg) = throwError $ "Decode error: " ++ msg
parseToDecode (Right a) = pure a
