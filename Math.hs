

---------------------------------------------------------------
-- Copyright (c) 2014, Enzo Haussecker. All rights reserved. --
---------------------------------------------------------------

{-# LANGUAGE LambdaCase #-}
{-# OPTIONS -Wall       #-}

-- | Parse and evaluate mathematical expressions.
module Math where

import Control.Applicative ((<|>))
import Control.Monad       (liftM, liftM2)
import Data.Char
import qualified Data.Map                           as M
import qualified Text.ParserCombinators.Parsec.Expr as P
import qualified Text.ParserCombinators.Parsec      as P

-- | Mathematical expressions.
data Expr = Num Integer
            | Ref String
            | Neg Expr
            | Add Expr Expr
            | Sub Expr Expr
            | Mul Expr Expr
            | Div Expr Expr
           deriving Show

build :: P.Parser Expr
build = do P.try $ P.buildExpressionParser table (P.try $ factor) <|> factor

table :: [[P.Operator Char st Expr]]
table =
  [ [ prefix "-" Neg ]
  , [ binary "*" Mul P.AssocLeft, binary "/ " Div P.AssocLeft ]
  , [ binary "+" Add P.AssocLeft, binary "-" Sub P.AssocLeft ]
  ] where binary s f a = P.Infix  (P.try (P.string s) >> ws >> return f) a
          prefix s f   = P.Prefix (P.try (P.string s) >> ws >> return f)

ws = P.many $ do {P.many1 (P.oneOf " \n"); return()}

factor ::P.Parser Expr
factor = do
  _    <- P.char '('
  expr <- build
  ws
  _    <- P.char ')'
  ws
  return (expr)
  <|> atom

atom :: P.Parser Expr
atom =  do P.try $ do {n <- number; ws; return(n)}
        <|>
        do var <- P.many1 (P.oneOf (['a'..'z'] ++ ['A'..'Z'] ++ ['_'] ++ ['0'..'9']))
           ws
           return $! Ref var

number :: P.Parser Expr
number = do
  digits <- P.many1 P.digit
  let n = foldl (\x d -> 10*x + toInteger (digitToInt d)) 0 digits
  ws
  return (Num n)
