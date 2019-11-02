module Elixir where

import Data.List
import qualified Text.Casing as Casing -- cabal install casing

import Head

generate :: Spec -> String
generate (Spec (Module h ds) i n) = let code = map definition (filter (not . (initOrNext i n)) ds)
                                        initialization = ini (findIdentifier i ds) h
                                        nextState = next (findIdentifier n ds)
                                    in header h ++ (intercalate "\n" (map ident (code ++ [nextState]))) ++ "\nend\n\n" ++ initialization

header :: Header -> String
header (Header i doc) = "defmodule " ++ pascal i ++ " do\n" ++ moduleDoc doc

moduleDoc doc = "@moduledoc \"\"\"\n" ++ (intercalate "\n" doc) ++ "\n\"\"\"\n"

funDoc doc = "@doc \"\"\"\n" ++ (intercalate "\n" doc) ++ "\n\"\"\"\n"
comment doc = intercalate "\n" (map ((++) "# ") doc) ++ "\n"

ini (Definition _ _ doc a) (Header i _) = comment doc ++ pascal i ++ ".main(%{\n" ++ intercalate ",\n" (conditionsToVariables (pascal i) a) ++ "\n})\n"

next (Definition _ _ doc a) = let (conditions, actions) = actionsAndConditions [] a
                              in funDoc doc ++ "def main(variables) do\n" ++ intercalate "\n" (conditions ++ actions) ++ "\nend\n"

initOrNext :: String -> String -> Definition -> Bool
initOrNext i n d = (isNamed i d) || (isNamed n d)

definition :: Definition -> String
definition (Definition i ps doc a) = let (conditions, actions) = actionsAndConditions ps a
                                      in funDoc doc ++ declaration (i ++ "Condition") ps ++ condition ps conditions ++ "\nend\n\n" ++ declaration i ps ++ action ps actions ++ "\nend\n\n"
definition (Comment s) = "# " ++ s

declaration i ps =  "def " ++ snake i ++ "(" ++ parameters ps ++ ") do\n"

condition :: [Parameter] -> [String] -> String
condition _ [] = "True\n"
condition ps cs = identAndSeparate " and" cs

action :: [Parameter] -> [String] -> String
action ps [] = "variables"
action ps as = let (otherActions, actions) = partition preassignment as
                   initialVariables = case actions of
                                        [] -> "variables"
                                        _ -> "%{\n" ++ identAndSeparate "," actions ++ "\n}\n"
               in intercalate " |> " (initialVariables:otherActions)

actionsAndConditions :: [Parameter] -> Action -> ([String], [String])
actionsAndConditions ps (Condition p) = (predicate ps p, [])
actionsAndConditions ps (Primed i v) = ([], [i ++ ": " ++ value ps v])
actionsAndConditions _ (Unchanged is) = ([], map unchanged is)
actionsAndConditions ps (ActionAnd as) = unzipAndFold (map (actionsAndConditions ps) as)
actionsAndConditions _ (ActionCall i ps) = ([call (i ++ "Condition") ("variables":ps)], [call i ps])
actionsAndConditions ps (ActionOr as) = ([], [decide ps (map (actionsAndConditions ps) as)])

-- Used for Init definition
conditionsToVariables :: Identifier -> Action -> [String]
conditionsToVariables m (Condition p) = case p of
                                      (Equality v1 v2) -> case v1 of
                                                           (Variable i) -> [i ++ ": " ++ value [] v2]
                                                           -- (Constant c) -> [m ++ ".constants[:" ++ c ++ "]"]
                                                           (SetValue (Ref i)) -> [i ++ ": " ++ value [] v2]
                                                           _ -> error("Init condition ambiguous: " ++ show p)
                                      _ -> error("Init condition ambiguous: " ++ show p)
conditionsToVariables m (ActionAnd as) = foldr (++) [] (map (conditionsToVariables m) as)

unchanged i = i ++ ": variables[:" ++ snake i ++ "]"

call i [] = snake i
call i ps = snake i ++ "(" ++ intercalate ", " (ps) ++ ")"

predicate :: [Parameter] -> Predicate -> [String]
predicate ps (Equality v1 v2) = [value ps v1 ++ " == " ++ value ps v2]
predicate ps (Inequality v1 v2) = [value ps v1 ++ " != " ++ value ps v2]
predicate ps (RecordBelonging v1 v2) = ["Enum.member?(" ++ value ps v1 ++ ", " ++ value ps v2 ++ ")"]

decide :: [Parameter] -> [([String], [String])] -> String
decide ps ls = let conditionsAndActions = "conditions_and_actions = [\n" ++ intercalate ", " (map (conditionActionTuple ps) ls) ++ "\n]\n"
                   tryPossibilities = "possible_states = for {condition, action} <- conditions_and_actions,\n\
                                      \into: MapSet.new,\n\
                                      \do: if condition, do: action, else: nil\n\n\
                                      \possible_states = MapSet.delete(possible_states, nil)\n\n\
                                      \if MapSet.size(possible_states) == 1 do\n\
                                      \Enum.head(MapSet.to_list(possible_states))\n\
                                      \else\n\
                                      \raise 'Not enough information to decide'\n\
                                      \end\n"
              in "(\n" ++ conditionsAndActions ++ tryPossibilities ++ ")"

value :: [Parameter] -> Value -> String
value ps (Variable i) = variable ps i
value _ (Constant c) = "constants[:" ++ c ++ "]"
value ps (SetValue s) = set ps s
value ps (RecordValue r) = record ps r
value _ (LiteralValue l) = literal l
value ps (Index i k) = index ps i k

conditionActionTuple ps (cs, as) = "{\n  " ++ condition ps cs ++ ",\n  (" ++ action ps as ++ ")\n}"

parameters ps = intercalate ", " ("variables": ps)
extraParameters ps = intercalate ", " ps

set ps (Set vs) = "MapSet.new([" ++ intercalate ", " (map (value ps) vs) ++ "])"
set ps (Ref i) = variable ps i
set ps (Union (Set [v]) s) = "MapSet.put(" ++ set ps s ++ ", " ++ value ps v ++ ")"
set ps (Union  s (Set [v])) = "MapSet.put(" ++ set ps s ++ ", " ++ value ps v ++ ")"
set ps (Union s1 s2) = "MapSet.union(" ++ set ps s1 ++ ", " ++ set ps s2 ++ ")"

record ps (Record rs) = intercalate " ++ " (map (mapping ps) rs) ++ " |> Enum.into(%{})"
record ps (Except i k v) = "Map.put(" ++ variable ps i ++ ", " ++ k ++ ", " ++ value ps v ++ ")"

mapping ps ((Key i), v) = "[{" ++ i ++ ", " ++ value ps v ++ "}]"
mapping ps ((All i a), v) = value ps a ++ " |> Enum.map(fn (" ++ i ++ ") -> {" ++ i ++ ", " ++ value ps v ++ "} end)"

literal (Str s) = show s
literal (Numb n) = show n

variable :: [Parameter] -> Identifier -> String
variable ps i = if elem i ps then snake i else "variables[:" ++ snake i ++ "]"

index ps i k = variable ps i ++ "[" ++ k ++ "]"

identAndSeparate sep ls = (intercalate (sep ++ "\n") (map ((++) "  ") ls))

unzipAndFold :: [([a],[b])] -> ([a],[b])
unzipAndFold = foldr (\x (a, b) -> (fst x ++ a, snd x ++ b)) ([],[])

snake i = Casing.toQuietSnake (Casing.fromAny i)
pascal i = Casing.toPascal (Casing.fromAny i)

ident block = intercalate "\n" (map ((++) "  ") (lines block))

preassignment as = (head as) == '(' || dropWhile (/= ':') as == []

isNamed i (Definition id _ _ _) = i == id
isNamed _ _ = False

findIdentifier i ds = case find (isNamed i) ds of
                        Just a -> a
                        Nothing -> error("Definition not found: " ++ (show i))
