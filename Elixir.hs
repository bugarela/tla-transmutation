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

ini (Definition _ _ doc a) (Header i _) = funDoc doc ++ pascal i ++ ".main()" -- TODO

next (Definition _ _ doc a) = funDoc doc ++ "def main(variables) do\n" -- TODO

initOrNext :: String -> String -> Definition -> Bool
initOrNext i n d = (isNamed i d) || (isNamed n d)

-- TODO: filter actions without actions
definition :: Definition -> String
definition (Definition i ps doc a) = let (conditions, actions) = actionsAndConditions ps a
                                      in funDoc doc ++ condition i ps conditions ++ action i ps actions ++ "end\n\n"
definition (Comment s) = "# " ++ s

condition :: Identifier -> [Parameter] -> [String] -> String
condition _ _ [] = ""
condition i ps cs = let declaration = "def " ++ snake i ++ "_condition(" ++ parameters ps ++ ") do\n" in
                      declaration ++ identAndSeparate " and" cs ++ "\nend\n\n"

action :: Identifier -> [Parameter] -> [String] -> String
action i ps as = let declaration = "def " ++ snake i ++ "(" ++ parameters ps ++ ") do\n" in
                   declaration ++ "%{\n" ++ identAndSeparate "," as ++ "\n}\n"

actionsAndConditions :: [Parameter] -> Action -> ([String], [String])
actionsAndConditions ps (Condition p) = (predicate ps p, [])
actionsAndConditions ps (Primed i v) = ([], [i ++ ": " ++ value ps v])
actionsAndConditions _ (Unchanged is) = ([], map unchanged is)
actionsAndConditions ps (ActionAnd as) = unzipAndFold (map (actionsAndConditions ps) as)

unchanged i = i ++ ": variables[:" ++ snake i ++ "]"

predicate :: [Parameter] -> Predicate -> [String]
predicate ps (Equality v1 v2) = [value ps v1 ++ " == " ++ value ps v2]
predicate ps (RecordBelonging v1 v2) = ["Enum.member?(" ++ value ps v1 ++ ", " ++ value ps v2 ++ ")"]

value :: [Parameter] -> Value -> String
value ps (Variable i) = variable ps i
value ps (SetValue s) = set ps s
value ps (RecordValue r) = record ps r
value _ (LiteralValue l) = literal l
value ps (Index i k) = index ps i k

parameters ps = intercalate ", " (ps ++ ["variables"])

set ps (Set vs) = "[" ++ intercalate ", " (map (value ps) vs) ++ "]"
set ps (Ref i) = variable ps i
set ps (Union s1 s2) = set ps s1 ++ " ++ " ++ set ps s2

record ps (Record rs) = let f(k,v) = k ++ ": " ++ value ps v in
                          "%{ " ++ intercalate ", " (map f rs) ++ " }"
record ps (Except i k v) = "Map.put(" ++ variable ps i ++ ", " ++ k ++ ", " ++ value ps v ++ ")"

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

isNamed i (Definition id _ _ _) = i == id
isNamed _ _ = False

findIdentifier i ds = case find (isNamed i) ds of
                        Just a -> a
                        Nothing -> error("Definition not found: " ++ (show i))
