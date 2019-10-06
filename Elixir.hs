module Elixir where

import Data.List

import Head

generate :: Module -> String
generate (Module h ds) = header h ++ intercalate "\n" (map definition ds)

header :: Header -> String
header (Header i doc) = "defmodule " ++ i ++ " do\n" ++ moduleDoc doc

moduleDoc doc = "@moduledoc \"\"\"\n" ++ (intercalate "\n" doc) ++ "\"\"\"\n"

funDoc doc = "@doc \"\"\"\n" ++ (intercalate "\n" doc) ++ "\"\"\"\n"

definition :: Definition -> String
definition (Definition i ps doc a) = let (conditions, actions) = actionsAndConditions a
                                     in funDoc doc ++ condition i ps conditions ++ action i ps actions ++ "end\n\n"

condition :: Identifier -> [Parameter] -> [String] -> String
condition _ _ [] = ""
condition i ps cs = let declaration = "def " ++ i ++ "_condition(" ++ parameters ps ++ " variables) do\n" in
                      declaration ++ (intercalate " and\n" cs)

action :: Identifier -> [Parameter] -> [String] -> String
action i ps as = let declaration = "def " ++ i ++ "(" ++ parameters ps ++ " variables) do\n" in
                   declaration ++ "%{\n" ++ (intercalate ",\n" as) ++ "}\n"

actionsAndConditions :: Action -> ([String], [String])
actionsAndConditions (Condition p) = (predicate p, [])
actionsAndConditions (Primed i v) = ([], [i ++ ": " ++ value v])
actionsAndConditions (Unchanged is) = ([], map unchanged is)
actionsAndConditions (ActionAnd as) = unzipAndFold (map actionsAndConditions as)

unchanged i = i ++ ": variables[:" ++ i ++ "]"

predicate :: Predicate -> [String]
predicate (Equality v1 v2) = [value v1 ++ " == " ++ value v2]
predicate (RecordBelonging v1 v2) = ["Enum.member?(" ++ value v1 ++ ", " ++ value v2 ++ ")"]

value :: Value -> String
value (Variable i) = "variables[:" ++ i ++ "]"
value (SetValue s) = set s
value (RecordValue r) = record r
value (LiteralValue l) = literal l

parameters = show
set s = show s
record r = show r
literal l = show l

unzipAndFold :: [([a],[b])] -> ([a],[b])
unzipAndFold = foldr (\x (a, b) -> (fst x ++ a, snd x ++ b)) ([],[])
