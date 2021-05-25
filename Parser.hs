module Parser where

import Text.Parsec
import Text.Parsec.Expr
import Math as Math -- cabal install ParserFunction
import qualified Text.Parsec.Token as Token
import Text.Parsec.Language
import Data.Char
import Head

import Control.Monad.Identity (Identity)

import Debug.Trace

ignore = many $ thingsToIgnore

thingsToIgnore = theorem <|> moduleInstance <|> extends <|> divisionLine <|> do{(oneOf " \n"); return()}

divisionLine = do try $ do {string "--"; many (char '-'); char '\n'; ignore; return()}

variablesDeclaration = do try $ do string "VARIABLE"
                                   optional (char 'S')
                                   ws
                                   vs <- identifier `sepBy` (try $ comma)
                                   ignore
                                   return (vs)

theorem = do try $ do {string "THEOREM"; ws; manyTill anyChar (char '\n'); ignore; return()}
moduleInstance = do try $ do {string "INSTANCE"; ws; identifier; ignore; return()}
extends = do try $ do {string "EXTENDS"; ws; identifier `sepBy` (try $ comma); ignore; return()}

identifier = many1 (oneOf (['a'..'z'] ++ ['A'..'Z'] ++ ['_'] ++ ['0'..'9']))
constant = do try $ do c <- oneOf ['A'..'Z']
                       cs <- many (oneOf (['a'..'z'] ++ ['A'..'Z'] ++ ['_'] ++ ['0'..'9']))
                       return (c:cs)

reserved = ",;.(){}\"/\\[]"
comma = do {ws; char ','; ws; return ()}
infOr = do {ws; string "\\/"; ws; return ()}
infAnd = do {ws; string "/\\"; ws; return ()}

parseFile a = do f <- readFile a
                 let e = parse specification "Error:" (f)
                 -- let e = parse arithmeticExpression "Error:" (f)
                 return e

specification = do (n, d) <- moduleHeader
                   ws
                   ds <- many definition
                   ws
                   many $ char '='
                   ignore
                   many comment
                   eof
                   return (Module n d, ds)

moduleHeader = do many (char '-')
                  string " MODULE "
                  name <- identifier
                  ws
                  divisionLine
                  documentation <- many comment
                  ignore
                  return (name, documentation)

comment = do try $ do string "(*"
             c <- anyChar `manyTill` (do try $ string "*)")
             ignore
             return (c)
          <|>
          do try $ do string "\\* "
             c <- anyChar `manyTill` (char '\n')
             ignore
             return (c)

declaration = do try $ do string "CONSTANT"
                          optional (char 'S')
                          ws
                          cs <- constant `sepBy` (try $ comma)
                          ignore
                          return (cs)

parameters = identifier `sepBy` comma

call = do try $ do i <- identifier
                   char '('
                   ws
                   ps <- value `sepBy` comma
                   char ')'
                   ignore
                   return (i, ps)
       <|>
       do try $ do i <- identifier
                   ws
                   return (i, [])

defSignature = do try $ do i <- identifier
                           char '('
                           ws
                           ps <- parameters
                           char ')'
                           ignore
                           return (i, ps)
       <|>
       do try $ do i <- identifier
                   ws
                   return (i, [])

definition = do {c <- comment; return (Comment c)}
             <|>
             do try $ do {cs <- declaration; return (Constants cs)}
             <|>
             do try $ do {cs <- variablesDeclaration; return (Variables cs)}
             <|>
             do try $ do i <- identifier
                         ws
                         string "=="
                         ws
                         v <- value
                         return (ValueDefinition i v)
             <|>
             do try $ do (i, ps) <- defSignature
                         string "=="
                         ws
                         doc <- many comment
                         a <- action
                         ignore
                         return (ActionDefinition i ps doc a)

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

action =  do string "IF"
             ws
             p <- predicate
             string "THEN"
             ws
             at <- action
             string "ELSE"
             ws
             af <- action
             return (If p at af)
         <|>
         do {p <- predicate; return (Condition p)}
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
         <|>
         do try $ do string "\\E"
                     ws
                     i <- identifier
                     ws
                     string "\\in"
                     ws
                     v <- value
                     char ':'
                     ws
                     as <- action `sepBy` infOr
                     return (Exists i v (ActionOr as))


predicate = do try $ do char '('
                        ws
                        ps <- atomPredicate `sepBy` infAnd
                        char ')'
                        ws
                        return (And ps)
           <|>
           do try $ do char '('
                       ws
                       ps <- atomPredicate `sepBy` infOr
                       char ')'
                       ws
                       return (Or ps)
           <|> atomPredicate

atomPredicate = do try $ do v1 <- value
                            char '='
                            ws
                            v2 <- value
                            return (Equality v1 v2)
                <|>
                do try $ do v1 <- value
                            char '#'
                            ws
                            v2 <- value
                            return (Inequality v1 v2)
                <|>
                do try $ do v1 <- value
                            char '>'
                            ws
                            v2 <- value
                            return (Gt v1 v2)
                <|>
                do try $ do v1 <- value
                            char '<'
                            ws
                            v2 <- value
                            return (Lt v1 v2)
                <|>
                do try $ do v1 <- value
                            string ">="
                            ws
                            v2 <- value
                            return (Gte v1 v2)
                <|>
                do try $ do v1 <- value
                            string "<="
                            ws
                            v2 <- value
                            return (Lte v1 v2)
                <|>
                do try $ do v1 <- value
                            string "\\in"
                            ws
                            v2 <- value
                            return (RecordBelonging v1 v2)
                <|>
                do try $ do v1 <- value
                            string "\\notin"
                            ws
                            v2 <- value
                            return (RecordNotBelonging v1 v2)
                <|>
                do try $ do string "\\A"
                            ws
                            (i, v, p) <- inFilter
                            return (ForAll i v p)

predicateConditionCall = do try $ do i <- identifier
                                     return (ConditionCall i [])

inFilter = do i <- identifier
              ws
              string "\\in"
              ws
              v <- value
              char ':'
              ws
              p <- predicate
              return (i, v, p)

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

value = do try $ do string "Cardinality("
                    ws
                    s <- set
                    char ')'
                    ws
                    return (Cardinality s)
        <|>
        do {c <- caseStatement; return (c)}
        <|>
        do try $ do {n1 <- Math.number; string ".."; n2 <- Math.number; ws; return (Range n1 n2)}
        <|>
        do {r <- record; return (r)}
        <|>
        do try $ do {i <- identifier; char '['; k <- identifier; char ']'; ws; return (Index (Arith (Ref i)) (Arith (Ref k)))}
        <|>
        do try $ do {i <- identifier; char '['; k <- literal; char ']'; ws; return (Index (Arith (Ref i)) k)}
        <|>
        do {s <- set; return (s)}
        <|>
        do try $ do {n1 <- Math.number; string ".."; n2 <- Math.number; ws; return (Range n1 n2)}
        <|>
        do try $ do {e <- arithmeticExpression; ws; return (Arith e)}
        <|>
        do {l <- literal; return (l)}

set = do try $ do {s1 <- atomSet; string "\\cup"; ws; s2 <- set; ws; return (Union s1 s2)}
      <|>
      atomSet

atomSet = do try $ do char '{'
                      vs <- value `sepBy` (try $ comma)
                      char '}'
                      ws
                      return (Set vs)
          <|>
          do try $ do char '{'
                      (i, v, p) <- inFilter
                      char '}'
                      ws
                      return (Filtered i v p)
          <|>
          do {e <- arithmeticExpression; ws; return (Arith e)}

caseMatch = do try $ do string "OTHER"
                        ws
                        string "->"
                        ws
                        v <- value
                        ws
                        return (DefaultMatch v)
           <|>
           do p <- (try $ predicate <|> predicateConditionCall)
              ws
              string "->"
              ws
              v <- value
              ws
              return (Match p v)

caseStatement = do try $ do string "CASE"
                            ws
                            cs <- caseMatch `sepBy` (try $ do {ws; string "[]"; ws})
                            ws
                            return (Case cs)

record = do try $ do char '['
                     ms <- mapping `sepBy` (try $ comma)
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

literal = do try $ do {char '\"'; cs <- many1 (noneOf reserved); char '\"'; ws; return (Str cs)}

arithmeticExpression = Math.build
