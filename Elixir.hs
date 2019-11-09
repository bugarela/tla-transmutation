module Elixir where

import Data.List
import Data.List.Extra
import qualified Text.Casing as Casing -- cabal install casing

import Head
import Snippets
import DocHandler

generate :: Spec -> String
generate (Spec m i n ds) = let defs = filter (not . (specialDef i n)) ds
                               cs = findConstants ds
                               defInit = findIdentifier i ds
                               defNext = findIdentifier n ds
                           in spec m cs defs defInit defNext

spec :: Module -> [Constant] -> [Definition] -> Init -> Next -> String
spec m cs ds di dn = let g = map (\c -> (c, "const")) cs
                         state = ini (g ++ moduleContext m) di
                     in concat [moduleHeader m,
                                ident (concat [
                                          mapAndJoin constant cs,
                                          mapAndJoin (definition g) ds,
                                          "\n",
                                          next g dn,
                                          decideAction
                                          ]
                                      ),
                                "\nend\n\n",
                                mainCall m state]

moduleHeader :: Module -> String
moduleHeader (Module i doc) = "defmodule " ++ pascal i ++ " do\n" ++ ident (moduleDoc doc ++ oracleDelaration)

moduleContext (Module m _) = [(m,"module")]

constant c =  let s = snake c in "@" ++ s ++ " \"<value for " ++ c ++ ">\"\ndef " ++ s ++ ", do: @" ++ s ++ "\n"

definition :: Context -> Definition -> String
definition g (Definition i ps doc a) = let g' = g ++ map (\p -> (p, "param")) ps
                                           (conditions, actions) = actionsAndConditions g' a
                                       in funDoc doc ++ declaration (i ++ "Condition") ps ++ ident (condition conditions) ++ "\nend\n\n" ++ declaration i ps ++ ident (action actions) ++ "\nend\n\n"
definition _ (Comment s) = "# " ++ cleanTrailing s

mainCall (Module i _) s = pascal i ++ ".main(\n" ++ ident s ++ "\n)\n"

ini g (Definition _ _ doc a) = comment doc ++ initialState g a

next g (Definition _ _ doc a) = let (_, actions) = actionsAndConditions g a
                                in funDoc doc ++ "def main(variables) do\n" ++ ident (logState ++ "main" ++ (action actions)) ++ "\nend\n" 


condition :: [String] -> String
condition [] = "True"
condition cs = intercalate " and " cs

action :: [String] -> String
action [] = "variables"
action as = let (otherActions, actions) = partition preassignment as
                kvs = intercalate ",\n" (map keyValue actions)
                initialVariables = case actions of
                                     [] -> []
                                     _ -> ["%{\n" ++ ident kvs ++ "\n}"]
            in mapMerge (initialVariables ++ otherActions)

actionName (ActionCall i ps) = i ++ "(" ++ intercalate ", " ps ++ ")"
actionName a = show a

actionsAndConditions :: Context -> Action -> ([String], [String])
actionsAndConditions g (Condition p) = (predicate g p, [])
actionsAndConditions g (Primed i v) = ([], ["%{ " ++ snake i ++ ": " ++ value g v ++ " }"])
actionsAndConditions _ (Unchanged is) = ([], [unchanged is])
actionsAndConditions g (ActionAnd as) = unzipAndFold (map (actionsAndConditions g) as)
actionsAndConditions _ (ActionCall i ps) = ([call (i ++ "Condition") ("variables":ps)], [call i ("variables":ps)])
actionsAndConditions g (ActionOr as) = ([], [decide g as])

initialState :: Context -> Action -> String
initialState g (ActionAnd as) = action (map (initialState g) as)
initialState g (Condition (Equality (Ref i) v)) = "%{ " ++ snake i ++ ": " ++ value g v ++ " }"
initialState _ p = error("Init condition ambiguous: " ++ show p)

unchanged is = let u = \i -> snake i ++ ": variables[:" ++ snake i ++ "]"
               in "%{ " ++ intercalate ",\n" (map u is) ++ " }"

call i [] = snake i
call i ps = snake i ++ "(" ++ intercalate ", " (ps) ++ ")"

predicate :: Context -> Predicate -> [String]
predicate g (Equality v1 v2) = [value g v1 ++ " == " ++ value g v2]
predicate g (Inequality v1 v2) = [value g v1 ++ " != " ++ value g v2]
predicate g (RecordBelonging v1 v2) = ["Enum.member?(" ++ value g v2 ++ ", " ++ value g v1 ++ ")"]

decide :: Context -> [Action] -> String
decide g as = let actionsMaps = map (actionMap g) as
                  list = "[\n" ++ ident (intercalate ",\n" actionsMaps) ++ "\n]\n"
              in "(\n" ++ ident ("decide_action(\n  \"Next\",\n" ++ ident list ++ "\n)\n") ++ "\n)"

actionMap g a = let (cs, as) = actionsAndConditions g a
                    n = "action: \"" ++ actionName a ++ "\""
                    c = "condition: " ++ condition cs
                    s = "state: " ++ action as
                in "%{ " ++ intercalate ", " [n,c,s] ++  " }"

value :: Context -> Value -> String
value g (Ref i) = reference g i
value g (Index i k) = index g i k
value g (Set vs) = "MapSet.new([" ++ intercalate ", " (map (value g) vs) ++ "])"
value g (Union (Set [v]) s) = "MapSet.put(" ++ value g s ++ ", " ++ value g v ++ ")"
value g (Union s (Set [v])) = "MapSet.put(" ++ value g s ++ ", " ++ value g v ++ ")"
value g (Union s1 s2) = "MapSet.union(" ++ value g s1 ++ ", " ++ value g s2 ++ ")"
value g (Record rs) = let (literals, generations) = partition isLiteral rs
                          m = intercalate " ++ " (map (mapping g) generations) -- merge
                          l = "%{ " ++ intercalate ", " (map (mapping g) literals) ++ " }"
                      in if m == [] then l else m ++ " |> Enum.into(" ++ l ++ ")"
value g (Except i k v) = "Map.put(" ++ reference g i ++ ", " ++ k ++ ", " ++ value g v ++ ")"
value _ (Str s) = show s
value _ (Numb n) = show n

reference g i = if elem (i, "param") g then i else
                  if elem (i, "const") g then cnst g i else
                    variable i

cnst g i = case dropWhile (\d ->snd d /= "module") g of
              [] -> "@" ++ snake i
              ms -> fst (head ms) ++ "." ++ snake i

parameters ps = intercalate ", " ("variables": ps)

isLiteral ((Key _), _) = True
isLiteral _ = False

mapping g ((Key i), v) = snake i ++ ": " ++ value g v
mapping g ((All i a), v) = value g a ++ " |> Enum.map(fn (" ++ i ++ ") -> {" ++ i ++ ", " ++ value g v ++ "} end)"


keyValue a = drop 3 (dropEnd 2 a)

mapMerge [m] = m
mapMerge (m:ms) = "Map.merge(\n  " ++ m ++ ",\n" ++ ident (mapMerge ms) ++ ")\n"

variable :: Identifier -> String
variable i = "variables[:" ++ snake i ++ "]"

declaration i ps =  "def " ++ snake i ++ "(" ++ parameters ps ++ ") do\n"

index ps i k = variable i ++ "[" ++ k ++ "]"

identAndSeparate sep ls = (intercalate (sep ++ "\n") (map ((++) "  ") ls))

unzipAndFold :: [([a],[b])] -> ([a],[b])
unzipAndFold = foldr (\x (a, b) -> (fst x ++ a, snd x ++ b)) ([],[])

snake i = Casing.toQuietSnake (Casing.fromAny i)
pascal i = Casing.toPascal (Casing.fromAny i)

ident block = intercalate "\n" (map tabIfline (lines block))

mapAndJoin f ls = intercalate "\n" (map f ls)

tabIfline [] = []
tabIfline xs = "  " ++ xs

preassignment as = (head as) == '(' || dropWhile (/= ':') as == []

isNamed i (Definition id _ _ _) = i == id
isNamed _ _ = False

specialDef :: String -> String -> Definition -> Bool
specialDef _ _ (Constants _) = True
specialDef i n d = (isNamed i d) || (isNamed n d)

findConstants ds = concat (map (\d -> case d of {Constants cs -> cs; _ -> [] }) ds)

findIdentifier i ds = case find (isNamed i) ds of
                        Just a -> a
                        Nothing -> error("Definition not found: " ++ (show i))

