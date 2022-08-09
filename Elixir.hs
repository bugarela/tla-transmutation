{-# LANGUAGE TupleSections #-}
module Elixir where

import Data.List

import ConfigParser
import DocHandler
import Head
import Helpers
import Snippets

generate :: Spec -> DistributionConfig -> [(String, ElixirCode)]
generate (Spec m i n ds) (Config ps shared consts _ _ _ _ _ _ _ _) =
  let defs = filter (not . (specialDef i n)) ds
      cs = findConstants ds
      vs = findVariables ds
      header = moduleHeader (moduleName m) m shared False
      -- defNext = findIdentifier n ds
      base = baseSpec header cs vs defs consts
   in (moduleName m, base):map (generateForProcess m n vs cs defs) ps

generateStarter :: Spec -> String -> (String, ElixirCode)
generateStarter (Spec m i _ ds) name =
  let cs = findConstants ds
      vs = findVariables ds
      g = (moduleName m, "module"):map (, "const") cs ++ map (, "variable") vs
      state = ini (g ++ moduleContext m) (findIdentifier i ds)
   in (moduleName m ++ "_" ++ name, starterTask (moduleName m) name state)

generateForProcess ::
     Module -> String -> [Variable] -> [Constant] -> [Definition] -> ProcessConfig -> (String, ElixirCode)
generateForProcess m n vs cs defs (PConfig p as) =
  let name = moduleName m ++ "_" ++ p
      header = moduleHeader name m [] True
      defNext = ActionDefinition n [] [] (ActionOr as)
   in (name, spec (moduleName m) header cs vs [] defNext)


-- filterDefs :: [Call] -> [Definition] -> [Definition]
-- filterDefs is ds =
--   let actionNames = map fst is
   -- in filter (\d -> name d `elem` actionNames) ds

{-- \vdash --}
-- (MOD)
spec :: String -> String -> [Constant] -> [Variable] -> [Definition] -> Next -> ElixirCode
spec m h cs vs ds dn =
  let g = (m, "module"):map (\c -> (c, "const")) cs ++ map (\v -> (v, "variable")) vs
   in concat
        [ h
        , ident (concat [mapAndJoin (definition g) ds, "\n", next g dn, mainFunction])
        , "\nend\n\n"
        ]

baseSpec :: String -> [Constant] -> [Variable] -> [Definition] -> [ConstantConfig] -> ElixirCode
baseSpec h cs vs ds consts =
  let g = map (\c -> (c, "const")) cs ++ map (\v -> (v, "variable")) vs
   in concat
        [ h
        , ident (concat [constants cs consts, mapAndJoin (definition g) ds, "\n", decideAction, "\n", waitLockFunction])
        , "\nend\n\n"
        ]

{-- \vdash_const --}
-- (CONST)
constants :: [Constant] -> [ConstantConfig] -> ElixirCode
constants cs vs =
  unlines
    (map
       (\c ->
          let s = snake c
              (Constant _ val) = head (dropWhile (\(Constant n _) -> n /= c) vs)
              decl = "@" ++ s ++ " " ++ value [] val ++ "\n"
              acc = "def " ++ s ++ ", do: @" ++ s ++ "\n\n"
           in decl ++ acc)
       cs)

{-- \vdash_dec --}
-- (DEF)
definition :: Context -> Definition -> ElixirCode
definition g (ActionDefinition i ps doc a) =
  let g' = g ++ map (\p -> (p, "param")) ps
      (conditions, actions) = actionsAndConditions g' a
   in if actions == []
        then declaration (i ++ "Condition") ps ++ ident (cFold conditions) ++ "\nend\n\n"
        else funDoc doc ++
             declaration (i ++ "Condition") ps ++
             ident (cFold conditions) ++ "\nend\n\n" ++ declaration i ps ++ ident (aFold actions) ++ "\nend\n\n"
definition g (ValueDefinition i ps v) = declaration i ps ++ ident (value g v) ++ "\nend\n\n"
-- Comment translation, not specified
definition _ (Comment s) = "# " ++ cleanTrailing s

definitionName (ActionDefinition i _ _ _) = i
definitionName (ValueDefinition i _ _) = i

localDefinition g (ValueDefinition i ps v) = snake i ++ " = fn(variables" ++ intercalate "" (map ("," ++) ps) ++ ") -> " ++ value g v ++ "end"

{-- \vdash_d --}
actionsAndConditions :: Context -> Action -> ([ElixirCode], [ElixirCode])
-- (CALL)
actionsAndConditions g (ActionCall i ps) =
  ([call g (i ++ "Condition") ("variables" : map (value g) ps)], [call g i ("variables" : map (value g) ps)])
-- (AND)
actionsAndConditions g (ActionAnd as) =
  let (ics, ias) = unzipAndFold (map (actionsAndConditions g) as)
   in ( if allUnchanged as
          then ["false"]
          else [cFold ics]
      , ias)
-- (OR)
actionsAndConditions g (ActionOr as) =
  let (ics, ias) = unzipAndFold (map (actionsAndConditions g) as)
   in ( if allUnchanged as
          then ["false"]
          else [orFold ics]
      , if ias == []
          then []
          else [listActions g as])
-- (IF)
actionsAndConditions g (ActionIf p t e) =
  let cp = value g p
      (ct, at) = actionsAndConditions g t
      (ce, ae) = actionsAndConditions g e
      c =
        ifExpr
          cp
          (if isUnchanged t
             then "false"
             else cFold ct)
          (if isUnchanged e
             then "false"
             else cFold ce)
      a = ifExpr cp (aFold at) (aFold ae)
   in ([c], [a])
actionsAndConditions g (ActionLet ds a) = let (cs, as) = actionsAndConditions (g ++ map ((,"local") . definitionName) ds) a
                                              defs = unwords (map (localDefinition g) ds)
                                          in (defs:cs, defs:as)
-- (COND)
actionsAndConditions g (Condition p) = ([value g p], [])
-- [new] (EXT)
actionsAndConditions g (Exists i v a) =
  let ig = (i, "param") : g
      (ics, _) = actionsAndConditions ig a
      c = "Enum.any?(" ++ value ig v ++ ", fn (" ++ i ++ ") ->" ++ cFold ics ++ " end\n)"
   in ([c], [listActions ig [Exists i v a]])
-- [new]: must test
actionsAndConditions g (ForAll i v a) =
  let ig = (i, "param") : g
      (ics, ias) = actionsAndConditions ig a
      c = "Enum.all?(" ++ value ig v ++ ", fn (" ++ i ++ ") ->" ++ cFold ics ++ " end)"
   in ([c], ias)
-- (TRA)
actionsAndConditions g a = ([], [action g a])

listActions :: Context -> [Action] -> ElixirCode
listActions _ [] = ""
listActions g as =
  let infos = map (actionInfo g) as
   in "Enum.filter(\n  List.flatten([\n" ++ ident (intercalate ",\n" infos) ++ "\n]),\n  fn(action) -> action[:condition] end\n)"

-- decide :: Context -> [Action] -> ElixirCode
-- decide _ [] = ""
-- decide g as =
--   let infos = map (actionInfo g) as
--       list = "List.flatten([\n" ++ ident (intercalate ",\n" infos) ++ "\n])\n"
--    in "(\n" ++ ident ("decide_action(\n" ++ ident list ++ "\n)\n") ++ "\n)"

{-- \vdash_a --}
action :: Context -> Action -> ElixirCode
-- (ACT-PRIM)
action g (Primed i v) = "%{ " ++ snake i ++ ": " ++ value g v ++ " }"
-- (ACT-UNCH)
action _ (Unchanged is) =
  let u = \i -> snake i ++ ": variables[:" ++ snake i ++ "]"
   in "%{ " ++ intercalate ",\n" (map u is) ++ " }"
-- [new] needs testing
-- action g (Value v) = value g v
action _ a = error ("Missing action case: " ++ show a)

{-- \vdash_p --}
value :: Context -> Value -> ElixirCode
-- (PRED-EQ)
value g (Equality v1 v2) = value g v1 ++ " == " ++ value g v2
-- (PRED-INEQ)
value g (Inequality v1 v2) = value g v1 ++ " != " ++ value g v2
-- Similar rules
value g (Gt v1 v2) = value g v1 ++ " > " ++ value g v2
value g (Lt v1 v2) = value g v1 ++ " < " ++ value g v2
value g (Gte v1 v2) = value g v1 ++ " >= " ++ value g v2
value g (Lte v1 v2) = value g v1 ++ " <= " ++ value g v2
-- [new] (PRED-CALL)
value g (ConditionCall i ps) = call g i ("variables" : map (value g) ps)
-- (PRED-IN)
value g (RecordBelonging v1 v2) = "Enum.member?(" ++ value g v2 ++ ", " ++ value g v1 ++ ")"
-- [new] (PRED-NOTIN)
value g (RecordNotBelonging v1 v2) = "not " ++ value g (RecordBelonging v1 v2)
-- (PRED-NOT)
value g (Not p) = "not " ++ value g p
-- [new] (PRED-AND)
value g (And ps) = intercalate " and " (map (value g) ps)
-- [new] (PRED-OR)
value g (Or ps) = intercalate " or " (map (value g) ps)
value g (If c t e) = "(if " ++ value g c ++ ", do: " ++ value g t ++ ", else: " ++ value g e ++ ")"
-- [new] (PRED-ALL)
value g (PForAll i v p) = "Enum.all?(" ++ value g v ++ ", fn(" ++ i ++ ") -> " ++ value ((i, "param") : g) p ++ " end)"
value g (PExists i v p) = "Enum.any?(" ++ value g v ++ ", fn(" ++ i ++ ") -> " ++ value ((i, "param") : g) p ++ " end)"
-- (REC-INDEX)
value g (Index v k) = value g v ++ "[" ++ value g k ++ "]"
-- (SET-LIT)
value g (Set vs) = "MapSet.new([" ++ intercalate ", " (map (value g) vs) ++ "])"
-- (SET-UNION)
value g (Union (Set [v]) s) = "MapSet.put(" ++ value g s ++ ", " ++ value g v ++ ")"
value g (Union s (Set [v])) = "MapSet.put(" ++ value g s ++ ", " ++ value g v ++ ")"
value g (Union s1 s2) = "MapSet.union(" ++ value g s1 ++ ", " ++ value g s2 ++ ")"
-- [new] (SET-FILT)
value g (Filtered i v p) =
  "MapSet.new(Enum.filter(" ++ value g v ++ ", fn(" ++ i ++ ") -> " ++ value ((i, "param") : g) p ++ " end))"
-- [new] (SET-CAR)
value g (Cardinality s) = "Enum.count(" ++ value g s ++ ")"
value g (SetIn v s) = "MapSet.member?(" ++ value g s ++ ", " ++ value g v ++ ")"
value g (SetMinus s1 s2) = "MapSet.difference(" ++ value g s1 ++ ", " ++ value g s2 ++ ")"
value g (SetTimes s1 s2) = "(for x <- " ++ value g s1 ++ ", y <- " ++ value g s2  ++ ", do: {x, y})"
-- (REC-LIT) and (REC-EX), aggregated to ensure ordering
value g (Record rs) =
  let (literals, generations) = partition isLiteral rs
      m = intercalate " ++ " (map (mapping g) generations) -- merge
      l = "%{ " ++ intercalate ", " (map (mapping g) literals) ++ " }"
   in if m == []
        then l
        else m ++ " |> Enum.into(" ++ l ++ ")"
-- (REC-EXCEPT)
value g (Except i es) =
  intercalate "|>" (reference g i:map (\(k, v) -> "Map.put(" ++ value g k ++ ", " ++ value g v ++ ")") es)
value g (FunGen i s v) = "Map.new(" ++ value g s ++ ", fn(" ++ i ++ ") -> {" ++ i ++ ", " ++ value ((i, "param") : g) v ++ "} end)"
-- [new] (CASE)
value g (Case ms) = "cond do\n" ++ intercalate "\n" (map (caseMatch g) ms) ++ "\nend\n"
-- Others, not specified
value g (TupleVal [a]) = value g a
value g (TupleVal as) = "{" ++ intercalate ", " (map (value g) as) ++ "}"
value g (Range n1 n2) = value g n1 ++ ".." ++ value g n2
value g (Ref i) = reference g i
value g (Neg a) = "-" ++ value' g a
value g (Add a b) = value' g a ++ " + " ++ value' g b
value g (Sub a b) = value' g a ++ " - " ++ value' g b
value g (Mul a b) = value' g a ++ " * " ++ value' g b
value g (Div a b) = value' g a ++ " / " ++ value' g b
value g (Mod a b) = "rem(" ++ value' g a ++ ", " ++ value' g b ++ ")"
value g (Domain v) = "Map.keys(" ++ value g v ++ ")"
value _ (Lit l) = lit l
value _ v = error ("Missing value case: " ++ show v)

value' _ (Lit (Num d)) = show d
value' g (Ref i) = reference g i
value' g e = "(" ++ value g e ++ ")"

lit (Str s) = show s
lit (Num d) = show d
lit (Boolean b) =
  if b
    then "true"
    else "false"
lit (Tuple as) = "{" ++ intercalate ", " (map lit as) ++ "}"

{-- \vdash_init --}
initialState :: Context -> Value -> ElixirCode
-- (INIT-AND)
initialState g (And as) = aFold (map (initialState g) as)
-- (INIT-EQ)
initialState g (Equality (Ref i) v) = "%{ " ++ snake i ++ ": " ++ value g v ++ " }"
-- Restriction
initialState _ p = error ("Init condition ambiguous: " ++ show p)

-- Comment extraction
ini :: Context -> Definition -> ElixirCode
ini g (ValueDefinition _ _ a) = initialState g a
ini _ a = error("Expected init to have no actions, found: " ++ show a)

{-- \vdash_next --}
next :: Context -> Definition -> ElixirCode
-- (NEXT)
-- TODO: Handle nested non-determinism (in a single transaction)
next g (ActionDefinition _ _ doc a) =
  let (_, actions) = actionsAndConditions g a
   in if actions == [] then error(show (actionsAndConditions g a)) else funDoc doc ++ "def next(variables) do\n" ++ ident (head actions) ++ "\nend\n\n"
next _ a = error("Next should be an action, found: " ++ show a)

{-- \vdash_i -}
actionInfo :: Context -> Action -> ElixirCode
-- (INFO-EX)
actionInfo g (Exists i v (ActionOr as)) =
  let ig = (i, "param") : g
      l = map (actionInfo ig) as
      s = intercalate ",\n" l
   in "Enum.map(" ++ value ig v ++ ", fn (" ++ i ++ ") -> [\n" ++ ident s ++ "\n] end\n)"
actionInfo g (Exists i v a) =
  let ig = (i, "param") : g
      s = actionInfo ig a
   in "Enum.map(" ++ value ig v ++ ", fn (" ++ i ++ ") -> [\n" ++ ident s ++ "\n] end\n)"
-- (INFO-DEF)
actionInfo g a =
  let (cs, as) = actionsAndConditions g a
      n = "action: \"" ++ actionName a ++ "\""
      c = "condition: " ++ cFold cs
      s = "transition: fn (variables) -> " ++ aFold as ++ " end"
   in "%{ " ++ intercalate ", " [n, c, s] ++ " }"

caseMatch g (Match p v) = value g p ++ " -> " ++ value g v
caseMatch g (DefaultMatch v) = "true -> " ++ value g v

mapping g ((Key i), v) = lit i ++ " => " ++ value g v
mapping g ((All i a), v) =
  let ig = (i, "param") : g
   in value g a ++ " |> Enum.map(fn (" ++ i ++ ") -> {" ++ i ++ ", " ++ value ig v ++ "} end)"

-- (VAL-*)
reference g i =
  if elem (i, "param") g
    then i
    else if elem (i, "const") g
           then cnst g i
           else if elem (i, "variable") g
                  then "variables[:" ++ snake i ++ "]"
                  else i ++ "(variables)"

cnst g i =
  case dropWhile (\d -> snd d /= "module") g of
    [] -> "@" ++ snake i
    ms -> fst (head ms) ++ "." ++ snake i
