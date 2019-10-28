module Parser where

import Text.Parsec
import Text.Parsec.Expr
import qualified Text.Parsec.Token as Token
import Text.Parsec.Language
import Data.Char
import Head

import Control.Monad.Identity (Identity)

ws = many $ do {many1 (oneOf " \n"); many divisionLine; return()}

divisionLine = do {string "--"; many (char '-'); char '\n'; return()}

identifier = many1 (oneOf (['a'..'z'] ++ ['A'..'Z'] ++ ['_'] ++ ['0'..'9']))
reserved = ",;.(){}\"/\\[]"
comma = do {ws; char ','; ws; return ()}

parseFile a = do f <- readFile a
                 let e = parse specification "Error:" (f)
                 return e

specification = do h <- moduleHeader
                   ws
                   ds <- many definition
                   ws
                   many $ char '='
                   ws
                   eof
                   return (Module h ds)

moduleHeader = do many (char '-')
                  string " MODULE "
                  name <- identifier
                  ws
                  documentation <- many comment
                  ws
                  return (Header name documentation)

comment = do string "(*"
             c <- anyChar `manyTill` (do try $ string "*)")
             ws
             return (c)

parameters = identifier `sepBy` comma

call = do try $ do i <- identifier
                   char '('
                   ws
                   ps <- parameters
                   char ')'
                   ws
                   return (i, ps)
       <|>
       do try $ do i <- identifier
                   ws
                   return (i, [])


definition = do {c <- comment; return (Comment c)}
             <|>
             do try $ do (i, ps) <- call
                         string "=="
                         ws
                         doc <- many comment
                         a <- action
                         ws
                         return (Definition i ps doc a)

orAction = do string "\\/"
              ws
              a <- action
              ws
              return a

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
         do {(i, ps) <- call; return (ActionCall i ps)}
         <|>
         do try $ do {ws; as <- many1 andAction; return (ActionAnd as)}
         <|>
         do try $ do {ws; as <- many1 orAction; return (ActionOr as)}

predicate = do try $ do v1 <- value
                        char '='
                        ws
                        v2 <- value
                        return (Equality v1 v2)
            <|>
            do try $ do v1 <- value
                        string "\\in"
                        ws
                        v2 <- value
                        return (RecordBelonging v1 v2)

mapping = do try $ do ws
                      i <- identifier
                      ws
                      string "\\in"
                      ws
                      a <- value
                      ws
                      string "|->"
                      ws
                      v <- value
                      ws
                      return (All i a, v)
          <|>
          do ws
             i <- identifier
             ws
             string "|->"
             ws
             v <- value
             ws
             return (Key i, v)

primed = do try $ do i <- identifier
                     char '\''
                     ws
                     return (i)

value = do {l <- literal; return (LiteralValue l)}
        <|>
        do {r <- record; return (RecordValue r)}
        <|>
        do try $ do {i <- identifier; char '['; k <- identifier; char ']'; ws; return (Index i k)}
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

record = do try $ do char '['
                     ms <- mapping `sepBy` comma
                     char ']'
                     ws
                     return (Record ms)
         <|>
         do char '['
            i <- identifier
            ws
            string "EXCEPT"
            ws
            string "!["
            k <- identifier
            char ']'
            ws
            char '='
            ws
            v <- value
            char ']'
            ws
            return (Except i k v)

literal = do try $ do n <- number
                      return (Numb n)
          <|>
          do try $ do {char '\"'; cs <- many1 (noneOf reserved); char '\"'; ws; return (Str cs)}

number = do try $ do f <- Token.float (Token.makeTokenParser emptyDef)
                     ws
                     return (f)
         <|>
         do try $ do digits <- many1 digit
                     let n = foldl (\x d -> 10*x + fromIntegral (digitToInt d)) 0 digits
                     ws
                     return (n)
