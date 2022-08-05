{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Core.Parse where

import Control.Monad.Trans as Trans
import Data.Char as Char
import qualified Language.Haskell.Meta.Parse as MP
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Ppr (pprint)
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax hiding (lift)
import Tactic.Core.Debug
import Tactic.Core.Syntax
import Tactic.Core.Utility
import qualified Text.Parsec as P
import Prelude hiding (exp)

type Parser a = P.ParsecT String () Q a

runParser :: Parser a -> String -> Q a
runParser p str =
  P.runParserT p () "SourceName" str >>= \case
    Left err -> error $ show err
    Right a -> pure a

parseInstrs :: Parser [Instr]
parseInstrs = do
  instrs <- concat <$> parseInstr `P.sepBy` parseSymbol ";"
  P.optionMaybe . P.try $ parseSymbol ";" -- because why not
  pure instrs

-- intros of the form `[x1 x2 ... xn | ... | y1 y2 ... ym ]`
parseIntros :: Parser [[String]]
parseIntros = do
  parseSymbol "["
  -- s <- parseUntilBefore (parseIsChar ']')
  -- let intros = fmap (splitByChar ' ') . splitByChar '|' $ s
  intros <- (parseNameString `P.sepBy` P.spaces) `P.sepBy` (lexeme (P.char '/'))
  parseSymbol "]"
  pure intros

-- `[x1, x2, ...]:`
parseRequires :: Parser (Maybe [String])
parseRequires = P.optionMaybe . P.try $ do
  parseSymbol "["
  requires <- parseNameString `P.sepBy` parseSymbol ","
  parseSymbol "]:"

  pure requires

parseFlags :: Parser [String]
parseFlags = do
  mb_start <- P.optionMaybe $ P.try $ parseSymbol "#["
  case mb_start of
    Just _ -> do
      flags <- parseWord `P.sepBy` parseSymbol ","
      parseSymbol "]"
      pure flags
    Nothing ->
      pure []

parseInstrRequires :: [String] -> Parser [Instr]
parseInstrRequires requires =
  P.choice . fmap P.try $
    [ -- Assert
      do
        parseSymbol "assert"
        exp <- lexeme parseExp
        pure [Assert {exp, requires}],
      -- Dismiss
      do
        parseSymbol "dismiss"
        exp <- lexeme parseExp
        pure [Dismiss {exp, requires}],
      -- Use
      do
        parseSymbol "use"
        exp <- lexeme parseExp
        pure [Use {exp, requires}],
      -- Cond
      do
        parseSymbol "condition"
        exp <- lexeme parseExp
        pure [Cond {exp, requires}],
      -- error
      do
        error "only these tactics allow a scope guard: assert, dismiss, use, condition"
    ]

parseInstr :: Parser [Instr]
parseInstr = do
  parseRequires >>= \case
    Just requires -> parseInstrRequires requires
    Nothing -> parseInstr'

parseInstr' :: Parser [Instr]
parseInstr' =
  P.choice . fmap P.try $
    [ -- Intro
      do
        parseSymbol "intro"
        name <- parseNameString
        pure [Intro {name}],
      -- Destruct
      do
        parseSymbol "destruct"
        name <- parseNameString
        intros <- P.optionMaybe . P.try $ do
          parseSymbol "as"
          parseIntros
        flags <- parseFlags
        pure [Destruct {name, intros, flags}],
      -- Induct
      do
        parseSymbol "induct"
        name <- parseNameString
        intros <- P.optionMaybe . P.try $ do
          parseSymbol "as"
          parseIntros
        flags <- parseFlags
        pure [Induct {name, intros, flags}],
      -- Auto
      do
        parseSymbol "auto"
        mb_hints <- P.optionMaybe . P.try $ do
          parseSymbol "["
          hints <- fmap nameToExp <$> P.sepBy parseName (parseSymbol ",")
          parseSymbol "]"
          pure hints
        mb_depth <- P.optionMaybe . P.try $ parseInt
        pure [Auto {hints = maybe defaultAutoHints id mb_hints, depth = maybe defaultAutoDepth id mb_depth}],
      -- Assert
      do
        parseSymbol "assert"
        exp <- lexeme parseExp
        pure [Assert {exp, requires = []}],
      -- Dismiss
      do
        parseSymbol "dismiss"
        exp <- lexeme parseExp
        pure [Dismiss {exp, requires = []}],
      -- Use
      do
        parseSymbol "use"
        exp <- lexeme parseExp
        pure [Use {exp, requires = []}],
      -- Cond
      do
        parseSymbol "condition"
        exp <- lexeme parseExp
        pure [Cond {exp, requires = []}],
      -- Trivial
      do
        parseSymbol "trivial"
        pure [Trivial],
      -- comment
      do
        P.spaces
        P.string "--"
        P.manyTill P.anyChar (P.try P.newline)
        pure []
    ]

parseDecInstrs :: Parser (Environment, [Instr])
parseDecInstrs = do
  -- sig
  P.spaces
  def_name <- parseName
  P.string "::"
  P.many $ P.char ' '
  def_type_string <- parseUntilBefore parseNextIsNewline
  def_type <- fromMP $ MP.parseType def_type_string
  let (def_argTypes, _) = flattenType def_type
  -- imp
  _ <- parseName -- == def_name
  def_argNames <- P.many parseName
  parseSymbol "="
  instrs <- parseInstrs
  pure
    ( emptyEnvironment
        { def_name = def_name,
          def_type = def_type,
          def_argNames = def_argNames,
          def_argTypes = def_argTypes
        },
      ((\name -> Intro {name = show name}) <$> def_argNames)
        ++ instrs
    )

fromMP :: Either String a -> Parser a
fromMP e = case e of
  Right a -> pure a
  Left msg -> error $ "metaparse: " ++ msg

lexeme :: Parser a -> Parser a
lexeme p = do
  a <- p
  P.spaces
  pure a

parseSymbol :: String -> Parser String
parseSymbol = lexeme . P.string

-- characters allowed in ids
parseNameChar :: Parser Char
parseNameChar = P.alphaNum P.<|> P.oneOf "_'"

parseName :: Parser Name
parseName = lexeme do
  s <- P.many1 parseNameChar
  pure $ mkName s

parseNameString :: Parser String
parseNameString = lexeme do
  P.many1 parseNameChar

parseWord :: Parser String
parseWord = lexeme do
  P.many1 P.alphaNum

parseInt :: Parser Int
parseInt = lexeme do
  ds <- P.many1 P.digit
  pure $ read ds

parseIsChar :: Char -> Parser Bool
parseIsChar c = do
  c' <- P.anyChar
  pure $ c == c'

parseExp :: Parser Exp
parseExp = do
  rest <- lookAheadRest
  debugM $ "parseExp: " ++ rest
  -- str <- P.between (parseSymbol "{") (parseSymbol "}") (P.many1 P.anyChar)
  parseSymbol "{"
  str <- P.manyTill P.anyChar (P.try (parseSymbol "}"))
  debugM $ "str: " ++ str
  fromMP (MP.parseExp str)

parseNextIsNewline :: Parser Bool
parseNextIsNewline = do
  c <- P.lookAhead P.anyChar
  pure $ c == '\n'

-- parses the string until right before `p` parses `True`
parseUntilBefore :: Parser Bool -> Parser String
parseUntilBefore p = lexeme go
  where
    go = do
      b <- P.lookAhead p
      if b
        then pure ""
        else do
          c <- P.anyChar
          (c :) <$> go

lookAheadRest :: Parser String
lookAheadRest = P.lookAhead (P.many P.anyChar)

splitByChar :: Char -> String -> [String]
splitByChar sep str = go "" str
  where
    go "" "" = []
    go acc "" = [acc]
    go acc (c : str)
      | c == sep = acc : go "" str
      | otherwise = go (acc ++ [c]) str
