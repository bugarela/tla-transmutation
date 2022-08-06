---------------------------------------------------------------
-- Copyright (c) 2014, Enzo Haussecker. All rights reserved. --
---------------------------------------------------------------
{-# OPTIONS -Wall       #-}

-- | Parse and evaluate mathematical expressions.
module Math where

import Control.Applicative ((<|>))

import Data.Char
import Head

import qualified Text.ParserCombinators.Parsec as P
import qualified Text.ParserCombinators.Parsec.Expr as P

build :: P.Parser Value
build = do
  P.try $ P.buildExpressionParser table (P.try $ factor) <|> factor

table :: [[P.Operator Char st Value]]
table =
  [ [prefix "-" Neg]
  , [binary "*" Mul P.AssocLeft, binary "/ " Div P.AssocLeft]
  , [binary "+" Add P.AssocLeft, binary "-" Sub P.AssocLeft]
  , [binary "%" Mod P.AssocLeft]
  ]
  where
    binary s f a = P.Infix (P.try (P.string s) >> ws >> return f) a
    prefix s f = P.Prefix (P.try (P.string s) >> ws >> return f)

ws =
  P.many $ do
    P.many1 (P.oneOf " \n")
    return ()

factor :: P.Parser Value
factor =
  do _ <- P.char '('
     expr <- build
     ws
     _ <- P.char ')'
     ws
     return (expr)
     <|> atom

atom :: P.Parser Value
atom =
  do P.try $ do
       n <- number
       ws
       return (n)
     <|> do
    var <- P.many1 (P.oneOf (['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['_'] ++ ['0' .. '9']))
    ws
    return $! Ref var

number :: P.Parser Value
number = do
  n <- numberLiteral
  return (Lit n)

numberLiteral :: P.Parser Lit
numberLiteral = do
  digits <- P.many1 P.digit
  let n = foldl (\x d -> 10 * x + toInteger (digitToInt d)) 0 digits
  ws
  return (Num n)
