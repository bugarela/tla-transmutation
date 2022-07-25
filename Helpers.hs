module Helpers where

import Data.List
import Data.List.Extra
import qualified Text.Casing as Casing -- cabal install casing

import DocHandler
import Head
import Snippets

-- (MOD) helpers
moduleHeader name (Module m doc) shared imp =
  "defmodule " ++
  name ++
  " do\n" ++
  ident
    (moduleDoc doc ++
     sharedVariablesDeclaration shared ++
     oracleDelaration ++
     if imp
       then "import " ++ m ++ "\n\n"
       else "")

sharedVariablesDeclaration :: [String] -> String
sharedVariablesDeclaration [] = ""
sharedVariablesDeclaration shared =
  unlines ([ "def shared_variables do", "  [" ] ++ map (\v -> "    :" ++ v ++ ",") shared ++ ["  ]", "end"])

moduleContext (Module m _) = [(m, "module")]

-- (CALL) helpers
call i [] = snake i
call i ps = snake i ++ "(" ++ intercalate ", " ps ++ ")"

-- (IF) helpers
ifExpr c t e = "(if " ++ c ++ ", do: " ++ t ++ ", else: " ++ e ++ ")"

-- (REC-LIT) helpers
isLiteral ((Key _), _) = True
isLiteral _ = False

-- (INFO-*) helpers
actionName (ActionCall i ps) = i ++ "(" ++ intercalate ", " (map interpolate ps) ++ ")"
actionName a = escape (show a)

escape cs = foldr (++) "" (map escape' cs)

escape' :: Char -> String
escape' c
  | c `elem` regexChars = '\\' : [c]
  | otherwise = [c]
  where
    regexChars = "\\+()^$.{}]|\""

-- Others
enclose s = "(" ++ s ++ ")"

cFold :: [ElixirCode] -> ElixirCode
cFold [] = "true"
cFold [c] = c
cFold cs = "Enum.all?([" ++ intercalate ", " cs ++ "])"

aFold :: [ElixirCode] -> ElixirCode
aFold [] = "%{}"
aFold as =
  let (otherActions, actions) = partition preassignment as
      kvs = intercalate ",\n" (map keyValue actions)
      initialVariables =
        case actions of
          [] -> []
          _ -> ["%{\n" ++ ident kvs ++ "\n}"]
   in mapMerge (initialVariables ++ otherActions)

orFold :: [ElixirCode] -> ElixirCode
orFold [] = "true"
orFold [c] = c
orFold cs = "Enum.any?([" ++ intercalate ", " cs ++ "])"

isUnchanged (Unchanged _) = True
isUnchanged _ = False

allUnchanged xs = dropWhile isUnchanged xs == []

keyValue a = drop 3 (dropEnd 2 a)

mapMerge [m] = m
mapMerge (m:ms) = "Map.merge(\n  " ++ m ++ ",\n" ++ ident (mapMerge ms) ++ ")\n"

preassignment as =
  (head as) == '(' ||
  take 2 as == "if" || dropWhile (/= ':') as == [] || take 4 as == "Enum" || take 3 as == "Map" || take 4 as == "List"

interpolate (Lit (Str i)) = "#{inspect " ++ i ++ "}"
interpolate (Ref i) = "#{inspect " ++ i ++ "}"
interpolate i = show i

declaration i ps = "def " ++ snake i ++ "(" ++ intercalate ", " ("variables" : ps) ++ ") do\n"

identAndSeparate sep ls = (intercalate (sep ++ "\n") (map ((++) "  ") ls))

unzipAndFold :: [([a], [b])] -> ([a], [b])
unzipAndFold = foldr (\x (a, b) -> (fst x ++ a, snd x ++ b)) ([], [])

snake i = Casing.toQuietSnake (Casing.fromAny i)

pascal i = Casing.toPascal (Casing.fromAny i)

ident block = intercalate "\n" (map tabIfline (lines block))

mapAndJoin f ls = intercalate "\n" (map f ls)

tabIfline [] = []
tabIfline xs = "  " ++ xs

isNamed i (ActionDefinition id _ _ _) = i == id
isNamed i (ValueDefinition id _ _) = i == id
isNamed _ _ = False

name (ActionDefinition i _ _ _) = i
name (ValueDefinition i _ _) = i
name _ = ""

moduleName (Module i _) = i

partitionCondition (Condition c) = [c]
partitionCondition (ActionCall c ps) = [ConditionCall c ps]
partitionCondition (ActionOr cs) =
  let ics = foldr (++) [] (map partitionCondition cs)
   in if ics /= []
        then [Or ics]
        else []
partitionCondition (ActionAnd cs) =
  let ics = foldr (++) [] (map partitionCondition cs)
   in if ics /= []
        then [And ics]
        else []
partitionCondition (Exists i v (ActionOr cs)) =
  let ics = foldr (++) [] (map partitionCondition cs)
   in if ics /= []
        then [Or ics]
        else []
partitionCondition _ = []

specialDef :: String -> String -> Definition -> Bool
specialDef _ _ (Constants _) = True
specialDef _ _ (Variables _) = True
specialDef i n d = (isNamed i d) || (isNamed n d)

findConstants ds =
  concat
    (map
       (\d ->
          case d of
            Constants cs -> cs
            _ -> [])
       ds)

findVariables ds =
  concat
    (map
       (\d ->
          case d of
            Variables cs -> cs
            _ -> [])
       ds)

findIdentifier i ds =
  case find (isNamed i) ds of
    Just a -> a
    Nothing -> error ("Definition not found: " ++ show i ++ " in " ++ show ds)

starterTask name init =
  unlines
    [ "defmodule Mix.Tasks." ++ pascal (name ++ "Starter") ++ " do"
    , "  @moduledoc \"Printed when the user requests `mix help echo`\""
    , "  @shortdoc \"Echoes arguments\""
    , "  use Mix.Task"
    , "  import " ++ name
    , ""
    , "  @impl Mix.Task"
    , "  def run(_) do"
    , "      variables = %{}"
    , "      initial_state = " ++ init
    , ""
    , "    oracle = spawn(RandomOracle, :start, [initial_state, 0, nil])"
    , "    :global.register_name(\"oracle\", oracle)"
    , ""
    , "    ref = Process.monitor(oracle)"
    , ""
    , "     receive do"
    , "       {:DOWN, ^ref, _, _, _} ->"
    , "         IO.puts(\"Oracle is down\")"
    , "    end"
    , "  end"
    , "end"
    ]

tracerStarterTask name trace =
  unlines
    [ "defmodule Mix.Tasks.Startmodel do"
    , "  @moduledoc \"Printed when the user requests `mix help echo`\""
    , "  @shortdoc \"Echoes arguments\""
    , "  use Mix.Task"
    , ""
    , "  @impl Mix.Task"
    , "  def run(_) do"
    , "    trace =  ["
    ] ++
  trace ++
  unlines
    [ "    ]"
    , ""
    , "    oracle = spawn(TraceCheckerOracle, :start, [trace])"
    , "     " ++ name ++ ".main(oracle, Enum.at(trace, 0), 0)"
    , "  end"
    , "end"
    ]

toValue :: Action -> Value
toValue (ActionAnd as) = And (map toValue as)
toValue (Condition v) = v
toValue (ActionCall i ps) = ConditionCall i ps
toValue a = error("Not a value: " ++ show a)
