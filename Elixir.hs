module Elixir where

import Data.List

import Head

generate :: Module -> String
generate (Module h ds) = header h ++ intercalate "\n" (map definition ds)

header :: Header -> String
header (Header i doc) = "defmodule " ++ i ++ " do\n" ++ moduleDoc doc

moduleDoc doc = "@moduledoc \"\"\"\n" ++ (intercalate "\n" doc) ++ "\n\"\"\"\n"

funDoc doc = "@doc \"\"\"\n" ++ (intercalate "\n" doc) ++ "\n\"\"\"\n"

definition :: Definition -> String
definition (Definition i ps doc a) = let (conditions, actions) = actionsAndConditions ps a
                                     in funDoc doc ++ condition i ps conditions ++ action i ps actions ++ "end\n\n"

condition :: Identifier -> [Parameter] -> [String] -> String
condition _ _ [] = ""
condition i ps cs = let declaration = "def " ++ i ++ "_condition(" ++ parameters ps ++ ") do\n" in
                      declaration ++ (intercalate " and\n" cs) ++ "\nend\n\n"

action :: Identifier -> [Parameter] -> [String] -> String
action i ps as = let declaration = "def " ++ i ++ "(" ++ parameters ps ++ ") do\n" in
                   declaration ++ "%{\n" ++ (intercalate ",\n" as) ++ "\n}\n"

actionsAndConditions :: [Parameter] -> Action -> ([String], [String])
actionsAndConditions ps (Condition p) = (predicate ps p, [])
actionsAndConditions ps (Primed i v) = ([], [i ++ ": " ++ value ps v])
actionsAndConditions _ (Unchanged is) = ([], map unchanged is)
actionsAndConditions ps (ActionAnd as) = unzipAndFold (map (actionsAndConditions ps) as)

unchanged i = i ++ ": variables[:" ++ i ++ "]"

predicate :: [Parameter] -> Predicate -> [String]
predicate ps (Equality v1 v2) = [value ps v1 ++ " == " ++ value ps v2]
predicate ps (RecordBelonging v1 v2) = ["Enum.member?(" ++ value ps v1 ++ ", " ++ value ps v2 ++ ")"]

value :: [Parameter] -> Value -> String
value ps (Variable i) = variable ps i
value ps (SetValue s) = set ps s
value ps (RecordValue r) = record ps r
value _ (LiteralValue l) = literal l

parameters ps = intercalate ", " (ps ++ ["variables"])

set ps (Set vs) = "[" ++ intercalate ", " (map (value ps) vs) ++ "]"
set ps (Ref i) = variable ps i
set ps (Union s1 s2) = set ps s1 ++ " ++ " ++ set ps s2

record ps rs = let f(k,v) = k ++ ": " ++ value ps v in
                "%{ " ++ intercalate ", " (map f rs) ++ " }"

literal (Str s) = show s
literal (Numb n) = show n

variable :: [Parameter] -> Identifier -> String
variable ps i = if elem i ps then i else "variables[:" ++ i ++ "]"

unzipAndFold :: [([a],[b])] -> ([a],[b])
unzipAndFold = foldr (\x (a, b) -> (fst x ++ a, snd x ++ b)) ([],[])
