module Parser where

import Text.Parsec
import Text.Parsec.Expr
import qualified Text.Parsec.Token as Token
import Text.Parsec.Language
import Data.Char
import Head

import Control.Monad.Identity (Identity)

ws = do {many (oneOf " \n"); return()}

identifier = many (oneOf (['a'..'z'] ++ ['A'..'Z'] ++ ['_'] ++ ['0'..'9']))
reserved = ",;.(){}\"/\\"
comma = do {ws; char ','; ws; return ()}

parseFile a = do f <- readFile a
                 let e = parse specification "Error:" (f)
                 return e

specification = do h <- moduleHeader
                   ws
                   ds <- many definition
                   ws
                   many (char '=')
                   ws
                   eof
                   return (Module h ds)

moduleHeader = do many (char '-')
                  ws
                  string "MODULE"
                  ws
                  name <- identifier
                  ws
                  many (char '-')
                  ws
                  documentation <- many comment
                  many (char '-')
                  ws
                  return (Header name documentation)

comment = do string "(*"
             c <- anyChar `manyTill` (do try $ string "*)")
             ws
             return (c)

parameters = identifier `sepBy` comma

definition = do try $ do i <- identifier
                         char '('
                         ws
                         ps <- parameters
                         char ')'
                         ws
                         string "=="
                         ws
                         doc <- many comment
                         a <- action
                         ws
                         return (Definition i ps doc a)
             <|>
             do {c <- comment; return (Comment c)}

andAction = do string "/\\"
               ws
               a <- action
               ws
               return a

action = do {p <- predicate; return (Condition p)}
         <|>
         do {p <- primed; char '='; ws; v <- value; return (Primed p v)}
         <|>
         do string "UNCHANGED"
            ws
            string "<<"
            vs <- identifier `sepBy` (comma)
            string ">>"
            ws
            return (Unchanged vs)
         <|>
         do try $ do {ws; as <- many andAction; return (ActionAnd as)}

predicate = do try $ do v1 <- value
                        char '='
                        ws
                        v2 <- value
                        return (Equality v1 v2)
            <|>
            do char '['
               ms <- mapping `sepBy` comma
               char ']'
               ws
               string "\\in"
               ws
               i <- identifier
               return (RecordBelonging ms i)

mapping = do ws
             i <- identifier
             ws
             string "|->"
             ws
             v <- value
             ws
             return (i, v)

primed = do try $ do i <- identifier
                     char '\''
                     ws
                     return (i)

value = do {l <- literal; return (LiteralValue l)}
        <|>
        do {s <- set; return (SetValue s)}
        <|>
        do {i <- identifier; ws; return (Variable i)}

set = do try $ do {s1 <- atomSet; string "\\cup"; ws; s2 <- set; ws; return (Union s1 s2)}
      <|>
      atomSet

atomSet = do char '{'
             vs <- value `sepBy` comma
             char '}'
             ws
             return (Set vs)
          <|>
          do {i <- identifier; ws; return (Ref i)}

literal = do try $ do n <- number
                      return (Numb n)
          <|>
          do try $ do {char '\"'; cs <- many1 (noneOf reserved); char '\"'; ws; return (Str cs)}

number = do try $ do f <- Token.float (Token.makeTokenParser emptyDef)
                     ws
                     return (Decimal f)
         <|>
         do try $ do digits <- many1 digit
                     let n = foldl (\x d -> 10*x + toInteger (digitToInt d)) 0 digits
                     ws
                     return (Int n)
