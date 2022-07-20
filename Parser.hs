module Parser where

import Text.Parsec
import Math
import Control.Arrow
import Head

ignore = many thingsToIgnore

thingsToIgnore = theorem <|> moduleInstance <|> extends <|> divisionLine <|> do{oneOf " \n"; return()}

divisionLine = do try $ do {string "--"; many (char '-'); char '\n'; ignore; return()}

variablesDeclaration = do try $ do string "VARIABLE"
                                   optional (char 'S')
                                   ws
                                   vs <- identifier `sepBy` try comma
                                   ignore
                                   return vs

theorem = do try $ do {string "THEOREM"; ws; manyTill anyChar (char '\n'); ignore; return()}
moduleInstance = do try $ do {string "INSTANCE"; ws; identifier; ignore; return()}
extends = do try $ do {string "EXTENDS"; ws; identifier `sepBy` try comma; ignore; return()}

identifier = many1 (oneOf (['a'..'z'] ++ ['A'..'Z'] ++ ['_'] ++ ['0'..'9']))
constant = do try $ do c <- oneOf ['A'..'Z']
                       cs <- many (oneOf (['a'..'z'] ++ ['A'..'Z'] ++ ['_'] ++ ['0'..'9']))
                       return (c:cs)

reserved = ",;.(){}\"/\\[]"
comma = do {ws; char ','; ws; return ()}
infOr = do {ws; string "\\/"; ws; return ()}
infAnd = do {ws; string "/\\"; ws; return ()}

parseTla :: FilePath -> IO (Either String (Module, [Definition]))
parseTla a = do f <- readFile a
                let e = parse specification "Error:" f
                return (left show e)

parseCall c = parse call ("Error parsing " ++ c ++ ":") c

parseState s = parse action ("Error parsing " ++ s ++ ":") s

parseTrace t = parse trace ("Error parsing " ++ t ++ ":") t

trace = many1 $ do string "State "
                   _ <- many digit
                   string ": <"
                   _ <- manyTill anyChar (try (char '>'))
                   ignore
                   a <- action
                   ignore
                   return a


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
             return c
          <|>
          do try $ do string "\\* "
             c <- anyChar `manyTill` char '\n'
             ignore
             return c

declaration = do try $ do string "CONSTANT"
                          optional (char 'S')
                          ws
                          cs <- constant `sepBy` try comma
                          ignore
                          return cs

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

definition = do {Comment <$> comment;}
             <|>
             do try $ do {Constants <$> declaration;}
             <|>
             do try $ do {Variables <$> variablesDeclaration;}
             <|>
             do try $ do (i, ps) <- defSignature
                         ws
                         string "=="
                         ws
                         ValueDefinition i ps <$> value
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
             return (ActionIf p at af)
         <|>
         do {Condition <$> predicate;}
         <|>
         do {p <- primed; char '='; ws; Primed p <$> value;}
         <|>
         do string "UNCHANGED"
            ws
            string "<<"
            vs <- identifier `sepBy` comma
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
         <|>
         do try $ do string "\\A"
                     ws
                     i <- identifier
                     ws
                     string "\\in"
                     ws
                     v <- value
                     char ':'
                     ws
                     a <- action
                     return (ForAll i v a)


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
                            Equality v1 <$> value
                <|>
                do try $ do v1 <- value
                            char '#'
                            ws
                            Inequality v1 <$> value
                <|>
                do try $ do v1 <- value
                            char '>'
                            ws
                            Gt v1 <$> value
                <|>
                do try $ do v1 <- value
                            char '<'
                            ws
                            Lt v1 <$> value
                <|>
                do try $ do v1 <- value
                            string ">="
                            ws
                            Gte v1 <$> value
                <|>
                do try $ do v1 <- value
                            string "<="
                            ws
                            Lte v1 <$> value
                <|>
                do try $ do v1 <- value
                            string "\\in"
                            ws
                            RecordBelonging v1 <$> value
                <|>
                do try $ do v1 <- value
                            string "\\notin"
                            ws
                            v2 <- value
                            RecordNotBelonging v1 <$> value
                <|>
                do try $ do string "\\A"
                            ws
                            (i, v, p) <- inFilter
                            return (PForAll i v p)

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
             return (Key (Str i), v)

primed = do try $ do i <- identifier
                     char '\''
                     ws
                     return i

value = do try $ do string "Cardinality("
                    ws
                    s <- set
                    char ')'
                    ws
                    return (Cardinality s)
        <|>
        do {caseStatement;}
        <|>
        do try $ do {n1 <- Math.number; string ".."; n2 <- Math.number; ws; return (Range n1 n2)}
        <|>
        do {record;}
        <|>
        do try $ do {i <- identifier; char '['; k <- identifier; char ']'; ws; return (Index (Ref i) (Ref k))}
        <|>
        do try $ do {i <- identifier; char '['; k <- literal; char ']'; ws; return (Index (Ref i) k)}
        <|>
        do {set;}
        <|>
        do try $ do {n1 <- Math.number; string ".."; n2 <- Math.number; ws; return (Range n1 n2)}
        <|>
        do try $ do {e <- arithmeticExpression; ws; return (e)}
        <|>
        do {literal;}

set = do try $ do {s1 <- atomSet; string "\\cup"; ws; s2 <- set; ws; return (Union s1 s2)}
      <|>
      atomSet

atomSet = do try $ do char '{'
                      ws
                      vs <- value `sepBy` try comma
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
          do {e <- arithmeticExpression; ws; return (e)}

caseMatch = do try $ do string "OTHER"
                        ws
                        string "->"
                        ws
                        v <- value
                        ws
                        return (DefaultMatch v)
           <|>
           do p <- try $ predicate <|> predicateConditionCall
              ws
              string "->"
              ws
              v <- value
              ws
              return (Match p v)

caseStatement = do try $ do string "CASE"
                            ws
                            cs <- caseMatch `sepBy` try (do {ws; string "[]"; ws})
                            ws
                            return (Case cs)

record = do try $ do char '['
                     ms <- mapping `sepBy` try comma
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
            return (Except i [(Ref k, v)])

literal = do try $ do {char '\"'; cs <- many1 (noneOf reserved); char '\"'; ws; return (Lit (Str cs))}

arithmeticExpression = Math.build
