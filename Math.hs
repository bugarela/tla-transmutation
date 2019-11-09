

---------------------------------------------------------------
-- Copyright (c) 2014, Enzo Haussecker. All rights reserved. --
---------------------------------------------------------------

{-# LANGUAGE LambdaCase #-}
{-# OPTIONS -Wall       #-}

-- | Parse and evaluate mathematical expressions.
module Math where

import Control.Applicative ((<|>))
import Control.Monad       (liftM, liftM2)

import qualified Data.Map                           as M
import qualified Text.ParserCombinators.Parsec.Expr as P
import qualified Text.ParserCombinators.Parsec      as P

-- | Mathematical expressions.
data Expr a = Num      a
            | Var      String
            | Neg     (Expr a)
            | Add     (Expr a) (Expr a)
            | Sub     (Expr a) (Expr a)
            | Mul     (Expr a) (Expr a)
            | Div     (Expr a) (Expr a)
            | Pow     (Expr a) (Expr a)
            | Sqrt    (Expr a)
            | Exp     (Expr a)
            | Log     (Expr a)
            | Abs     (Expr a)
            | Sin     (Expr a)
            | Cos     (Expr a)
            | Tan     (Expr a)
            | Sec     (Expr a)
            | Csc     (Expr a)
            | Cot     (Expr a)
            | Sinh    (Expr a)
            | Cosh    (Expr a)
            | Tanh    (Expr a)
            | Sech    (Expr a)
            | Csch    (Expr a)
            | Coth    (Expr a)
            | ArcSin  (Expr a)
            | ArcCos  (Expr a)
            | ArcTan  (Expr a)
            | ArcSec  (Expr a)
            | ArcCsc  (Expr a)
            | ArcCot  (Expr a)
            | ArcSinh (Expr a)
            | ArcCosh (Expr a)
            | ArcTanh (Expr a)
            | ArcSech (Expr a)
            | ArcCsch (Expr a)
            | ArcCoth (Expr a) deriving Show

build :: Floating a => P.Parser (Expr a)
build = P.buildExpressionParser table (P.try $ factor)

table :: Floating a => [[P.Operator Char st (Expr a)]]
table =
  [ [ prefix "arcsinh" ArcSinh, prefix "arcsin" ArcSin, prefix "sinh" Sinh, prefix "sin" Sin ]
  , [ prefix "arccosh" ArcCosh, prefix "arccos" ArcCos, prefix "cosh" Cosh, prefix "cos" Cos ]
  , [ prefix "arctanh" ArcTanh, prefix "arctan" ArcTan, prefix "tanh" Tanh, prefix "tan" Tan ]
  , [ prefix "arcsech" ArcSech, prefix "arcsec" ArcSec, prefix "sech" Sech, prefix "sec" Sec ]
  , [ prefix "arccsch" ArcCsch, prefix "arccsc" ArcCsc, prefix "csch" Csch, prefix "csc" Csc ]
  , [ prefix "arccoth" ArcCoth, prefix "arccot" ArcCot, prefix "coth" Coth, prefix "cot" Cot ]
  , [ prefix "abs"  Abs  ]
  , [ prefix "exp"  Exp  ]
  , [ prefix "sqrt" Sqrt ]
  , [ prefix "log"  Log  ]
  , [ binary "^" Pow P.AssocRight ]
  , [ prefix "-" Neg ]
  , [ binary "*" Mul P.AssocLeft, binary "/ " Div P.AssocLeft ]
  , [ binary "+" Add P.AssocLeft, binary "-" Sub P.AssocLeft ]
  ] where binary s f a = P.Infix  (P.try (P.string s) >> ws >> return f) a
          prefix s f   = P.Prefix (P.try (P.string s) >> ws >> return f)

ws = P.many $ do {P.many1 (P.oneOf " \n"); return()}

factor :: Floating a => P.Parser (Expr a)
factor = do
  _    <- P.char '('
  expr <- build
  ws
  _    <- P.char ')'
  ws
  return (expr)
  <|> atom

atom :: Floating a => P.Parser (Expr a)
atom =  do P.try $ do {n <- number; ws; return(n)}
        <|>
        do var <- P.many1 (P.oneOf (['a'..'z'] ++ ['A'..'Z'] ++ ['_'] ++ ['0'..'9']))
           ws
           return $! Var var

number :: Floating a => P.Parser (Expr a)
number = do
  pr <- P.many1 P.digit
  let n = foldl stl 0 pr
  P.option (Num n) . P.try $ do
    _  <- P.char '.'
    su <- P.many1 P.digit
    return $! Num $ n + foldr str 0 su
    where stl a x = (ctn x - ctn '0') + a  * 10
          str x a = (ctn x - ctn '0'  + a) / 10
          ctn     = realToFrac . fromEnum

-- | Evaluate a mathematical expression
--   using the supplied atom definitions.
--
-- > >>> :m + Data.Complex Data.Map
-- > >>> let def = fromList [("pi", pi), ("i", 0 :+ 1)]
-- > >>> evaluate def . Just $ Add (Exp (Mul (Neg (Var "pi")) (Var "i"))) (Num 1.0)
-- > Just (0.0 :+ (-1.2246467991473532e-16))
--
evaluate
  :: Floating a
  => M.Map String a -- ^ Atom definitions.
  -> Maybe (Expr a) -- ^ Mathematical expression.
  -> Maybe a
evaluate def = \ case
  Just (Num    num) -> Just num
  Just (Var    var) -> M.lookup var def
  Just (Neg     e1) -> liftM  (negate     ) (evaluate def $ Just e1)
  Just (Add  e1 e2) -> liftM2 (+          ) (evaluate def $ Just e1) (evaluate def $ Just e2)
  Just (Sub  e1 e2) -> liftM2 (-          ) (evaluate def $ Just e1) (evaluate def $ Just e2)
  Just (Mul  e1 e2) -> liftM2 (*          ) (evaluate def $ Just e1) (evaluate def $ Just e2)
  Just (Div  e1 e2) -> liftM2 (/          ) (evaluate def $ Just e1) (evaluate def $ Just e2)
  Just (Pow  e1 e2) -> liftM2 (**         ) (evaluate def $ Just e1) (evaluate def $ Just e2)
  Just (Sqrt    e1) -> liftM  (** 0.5     ) (evaluate def $ Just e1)
  Just (Exp     e1) -> liftM  (exp        ) (evaluate def $ Just e1)
  Just (Log     e1) -> liftM  (log        ) (evaluate def $ Just e1)
  Just (Abs     e1) -> liftM  (abs        ) (evaluate def $ Just e1)
  Just (Sin     e1) -> liftM  (sin        ) (evaluate def $ Just e1)
  Just (Cos     e1) -> liftM  (cos        ) (evaluate def $ Just e1)
  Just (Tan     e1) -> liftM  (tan        ) (evaluate def $ Just e1)
  Just (Sec     e1) -> liftM  (inv . sin  ) (evaluate def $ Just e1)
  Just (Csc     e1) -> liftM  (inv . cos  ) (evaluate def $ Just e1)
  Just (Cot     e1) -> liftM  (inv . tan  ) (evaluate def $ Just e1)
  Just (Sinh    e1) -> liftM  (sinh       ) (evaluate def $ Just e1)
  Just (Cosh    e1) -> liftM  (cosh       ) (evaluate def $ Just e1)
  Just (Tanh    e1) -> liftM  (tanh       ) (evaluate def $ Just e1)
  Just (Sech    e1) -> liftM  (inv . sinh ) (evaluate def $ Just e1)
  Just (Csch    e1) -> liftM  (inv . cosh ) (evaluate def $ Just e1)
  Just (Coth    e1) -> liftM  (inv . tanh ) (evaluate def $ Just e1)
  Just (ArcSin  e1) -> liftM  (asin       ) (evaluate def $ Just e1)
  Just (ArcCos  e1) -> liftM  (acos       ) (evaluate def $ Just e1)
  Just (ArcTan  e1) -> liftM  (atan       ) (evaluate def $ Just e1)
  Just (ArcSec  e1) -> liftM  (inv . asin ) (evaluate def $ Just e1)
  Just (ArcCsc  e1) -> liftM  (inv . acos ) (evaluate def $ Just e1)
  Just (ArcCot  e1) -> liftM  (inv . atan ) (evaluate def $ Just e1)
  Just (ArcSinh e1) -> liftM  (asinh      ) (evaluate def $ Just e1)
  Just (ArcCosh e1) -> liftM  (acosh      ) (evaluate def $ Just e1)
  Just (ArcTanh e1) -> liftM  (atanh      ) (evaluate def $ Just e1)
  Just (ArcSech e1) -> liftM  (inv . asinh) (evaluate def $ Just e1)
  Just (ArcCsch e1) -> liftM  (inv . acosh) (evaluate def $ Just e1)
  Just (ArcCoth e1) -> liftM  (inv . atanh) (evaluate def $ Just e1)
  _                 -> Nothing
  where inv = (/) 1

