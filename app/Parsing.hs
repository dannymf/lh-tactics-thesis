module Parsing where

import Control.Monad as Monad
import Data.Char as Char
import Data.List as List
import Data.Maybe as Maybe
import Debug
import System.IO as IO
import System.Process as Process

splitAtFindIndex :: (a -> Bool) -> [a] -> Maybe ([a], [a])
splitAtFindIndex cond l = do
  i <- findIndex cond l
  return $ splitAt i l

splitAtPrefix :: Eq a => [a] -> [a] -> Maybe ([a], [a])
splitAtPrefix pre str =
  if pre `isPrefixOf` str
    then return ([], str)
    else case str of
      [] -> Nothing
      (c : str') -> do
        (str1, str2) <- splitAtPrefix pre str'
        return (c : str1, str2)

splitAtSuffix :: Eq a => [a] -> [a] -> Maybe ([a], [a])
splitAtSuffix suf str =
  case stripPrefix suf str of
    Just str' -> return (suf, str')
    Nothing ->
      case str of
        [] -> Nothing
        (c : str') -> do
          (str1, str2) <- splitAtSuffix suf str'
          return (c : str1, str2)

splitBys :: Eq a => [a] -> [a] -> [[a]]
splitBys seps = go []
  where
    go acc [] = if null acc then [] else [reverse acc]
    go acc (h : t) = if h `elem` seps then (if null acc then [] else [reverse acc]) ++ go [] t else go (h : acc) t

trimSpace :: String -> String
trimSpace = takeWhile (not . isSpace) . dropWhile isSpace

isTHMessage :: String -> Bool
isTHMessage l = "Splicing declarations" `isSuffixOf` l

isLHMessage :: String -> Bool
isLHMessage l = "****" `isPrefixOf` l

isBuildMessage :: String -> Bool
isBuildMessage l =
  or $
    map
      (`isPrefixOf` l)
      [ "Linking",
        "Preprocessing",
        "Building"
      ]

tail' :: [a] -> [a]
tail' [] = []
tail' (_ : l) = l

mapWithIndex :: (Int -> a -> b) -> [a] -> [b]
mapWithIndex f = go 0
  where
    go i [] = []
    go i (x : xs) = f i x : go (i + 1) xs

dropSpace :: String -> String
dropSpace = dropWhile isSpace

dropUntilSpace :: String -> String
dropUntilSpace = dropWhile (not . isSpace)

dropLogHeader :: String -> String
dropLogHeader str = case splitAtSuffix "lh-tactics     > " str of
  Just (_, str') -> str'
  Nothing -> case splitAtSuffix "lh-tactics-test> " str of
    Just (_, str') -> str'
    Nothing -> str

cleanLogString :: String -> String
cleanLogString =
  (foldl (.) id)
    [ filter ('\b' /=),
      dropLogHeader
    ]
