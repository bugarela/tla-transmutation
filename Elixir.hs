module Elixir where

import Data.List
import qualified Text.Casing as Casing -- cabal install casing

import Head
import Snippets

generate :: Spec -> String
generate (Spec (Module h ds) i n) = let code = map definition (filter (not . (initOrNext i n)) ds)
                                        initialization = ini (findIdentifier i ds) h
                                        nextState = next (findIdentifier n ds)
                                    in header h ++ (intercalate "\n" (map ident (code ++ [nextState, decideAction]))) ++ "\nend\n\n" ++ initialization

header :: Header -> String
header (Header i doc) = "defmodule " ++ pascal i ++ " do\n" ++ ident (moduleDoc doc ++ oracleDelaration)

moduleDoc doc = "@moduledoc \"\"\"\n" ++ (intercalate "\n" (map cleanTrailing doc)) ++ "\n\"\"\"\n"
oracleDelaration = "@oracle spawn(Oracle, :listen, [])\n\n"

funDoc doc = "@doc \"\"\"\n" ++ (intercalate "\n" (map cleanTrailing doc)) ++ "\n\"\"\"\n"
comment doc = intercalate "\n" (map (((++) "# ") . cleanTrailing) doc) ++ "\n"

ini (Definition _ _ doc a) (Header i _) = comment doc ++ pascal i ++ ".main(%{\n" ++ identAndSeparate "," (conditionsToVariables (pascal i) a) ++ "\n})\n"

next (Definition _ _ doc a) = let (_, actions) = actionsAndConditions [] a
                              in funDoc doc ++ "def main(variables) do\n" ++ ident(logState ++ "main(\n" ++ (intercalate "\n"  (actions)) ++ "\n)") ++ "\nend\n" -- Usar action e não intercalate

initOrNext :: String -> String -> Definition -> Bool
initOrNext i n d = (isNamed i d) || (isNamed n d)

definition :: Definition -> String
definition (Definition i ps doc a) = let (conditions, actions) = actionsAndConditions ps a
                                      in funDoc doc ++ declaration (i ++ "Condition") ps ++ ident (condition conditions) ++ "\nend\n\n" ++ declaration i ps ++ ident (action actions) ++ "\nend\n\n"
definition (Constants cs) = intercalate "\n" (map constant cs)
definition (Comment s) = "# " ++ cleanTrailing s

declaration i ps =  "def " ++ snake i ++ "(" ++ parameters ps ++ ") do\n"

condition :: [Parameter] -> String
condition [] = "True"
condition cs = intercalate " and " cs

action :: [String] -> String
action [] = "variables"
action as = let (otherActions, actions) = partition preassignment as
                initialVariables = case actions of
                                     [] -> []
                                     _ -> ["%{\n" ++ identAndSeparate "," actions ++ "\n}"]
            in merge (initialVariables ++ otherActions)

actionName (ActionCall i ps) = i ++ "(" ++ intercalate ", " ps ++ ")"
actionName a = show a

actionsAndConditions :: [Parameter] -> Action -> ([String], [String])
actionsAndConditions ps (Condition p) = (predicate ps p, [])
actionsAndConditions ps (Primed i v) = ([], [snake i ++ ": " ++ value ps v])
actionsAndConditions _ (Unchanged is) = ([], map unchanged is)
actionsAndConditions ps (ActionAnd as) = unzipAndFold (map (actionsAndConditions ps) as)
actionsAndConditions _ (ActionCall i ps) = ([call (i ++ "Condition") ("variables":ps)], [call i ("variables":ps)])
actionsAndConditions ps (ActionOr as) = ([], [decide ps as])

-- Used for Init definition
conditionsToVariables :: Identifier -> Action -> [String]
conditionsToVariables m (Condition p) = case p of
                                      (Equality v1 v2) -> case v1 of
                                                           (Variable i) -> [snake i ++ ": " ++ value [m] v2]
                                                           (SetValue (Ref i)) -> [snake i ++ ": " ++ value [m] v2]
                                                           _ -> error("Init condition ambiguous: " ++ show p)
                                      _ -> error("Init condition ambiguous: " ++ show p)
conditionsToVariables m (ActionAnd as) = foldr (++) [] (map (conditionsToVariables m) as)

unchanged i = snake i ++ ": variables[:" ++ snake i ++ "]"

call i [] = snake i
call i ps = snake i ++ "(" ++ intercalate ", " (ps) ++ ")"

predicate :: [Parameter] -> Predicate -> [String]
predicate ps (Equality v1 v2) = [value ps v1 ++ " == " ++ value ps v2]
predicate ps (Inequality v1 v2) = [value ps v1 ++ " != " ++ value ps v2]
predicate ps (RecordBelonging v1 v2) = ["Enum.member?(" ++ value ps v2 ++ ", " ++ value ps v1 ++ ")"]

decide :: [Parameter] -> [Action] -> String
decide ps as = let actionsMaps = map (actionMap ps) as
                   conditionsAndActions = "[\n" ++ ident (intercalate ",\n" actionsMaps) ++ "\n]\n"
               in ident ("decide_action(\n  \"Next\",\n" ++ ident conditionsAndActions ++ "\n)\n")

actionMap ps a = let (cs, as) = actionsAndConditions ps a
                     n = "action: \"" ++ actionName a ++ "\""
                     c = "condition: " ++ condition cs
                     s = "state: " ++ action as
                 in "%{ " ++ intercalate ", " [n,c,s] ++  " }"

value :: [Parameter] -> Value -> String
value ps (Variable i) = variable ps i
value [m] (Constant c) = m ++ "." ++ snake c -- outside module
value [] (Constant c) = "@" ++ snake c -- inside module
value ps (SetValue s) = set ps s
value ps (RecordValue r) = record ps r
value _ (LiteralValue l) = literal l
value ps (Index i k) = index ps i k

constant c = let s = snake c in "@" ++ s ++ " \"<value for " ++ c ++ ">\"\ndef " ++ s ++ ", do: @" ++ s

parameters ps = intercalate ", " ("variables": ps)
extraParameters ps = intercalate ", " ps

set ps (Set vs) = "MapSet.new([" ++ intercalate ", " (map (value ps) vs) ++ "])"
set ps (Ref i) = variable ps i
set ps (Union (Set [v]) s) = "MapSet.put(" ++ set ps s ++ ", " ++ value ps v ++ ")"
set ps (Union  s (Set [v])) = "MapSet.put(" ++ set ps s ++ ", " ++ value ps v ++ ")"
set ps (Union s1 s2) = "MapSet.union(" ++ set ps s1 ++ ", " ++ set ps s2 ++ ")"

record ps (Record rs) = let (literals, generations) = partition isLiteral rs 
                            g = intercalate " ++ " (map (mapping ps) generations) -- merge
                            l = "%{" ++ intercalate ", " (map (mapping ps) literals) ++ "}"
                        in if g == [] then l else g ++ " |> Enum.into(" ++ l ++ ")"
record ps (Except i k v) = "Map.put(" ++ variable ps i ++ ", " ++ k ++ ", " ++ value ps v ++ ")"

isLiteral ((Key _), _) = True
isLiteral _ = False

mapping ps ((Key i), v) = snake i ++ ": " ++ value ps v
mapping ps ((All i a), v) = value ps a ++ " |> Enum.map(fn (" ++ i ++ ") -> {" ++ i ++ ", " ++ value ps v ++ "} end)"

literal (Str s) = show s
literal (Numb n) = show n

merge [m] = m
merge (m:ms) = "Map.merge(\n  " ++ m ++ ",\n" ++ ident (merge ms) ++ ")\n"

variable :: [Parameter] -> Identifier -> String
variable ps i = if elem i ps then snake i else "variables[:" ++ snake i ++ "]"

index ps i k = variable ps i ++ "[" ++ k ++ "]"

identAndSeparate sep ls = (intercalate (sep ++ "\n") (map ((++) "  ") ls))

unzipAndFold :: [([a],[b])] -> ([a],[b])
unzipAndFold = foldr (\x (a, b) -> (fst x ++ a, snd x ++ b)) ([],[])

snake i = Casing.toQuietSnake (Casing.fromAny i)
pascal i = Casing.toPascal (Casing.fromAny i)

ident block = intercalate "\n" (map tabIfline (lines block))

tabIfline [] = []
tabIfline xs = "  " ++ xs

preassignment as = (head as) == '(' || dropWhile (/= ':') as == []

isNamed i (Definition id _ _ _) = i == id
isNamed _ _ = False

findIdentifier i ds = case find (isNamed i) ds of
                        Just a -> a
                        Nothing -> error("Definition not found: " ++ (show i))

allSpaces s = dropWhile (== ' ') s == []

cleanTrailing [] = []
cleanTrailing (x:xs) = if allSpaces xs then [x] else x:(cleanTrailing xs)
