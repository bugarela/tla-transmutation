module Elixir where

import Data.List
import Data.List.Extra

import Head
import Math
import Snippets
import DocHandler
import Helpers

generate :: Spec -> ElixirCode
generate (Spec m i n ds) = let defs = filter (not . (specialDef i n)) ds
                               cs = findConstants ds
                               vs = findVariables ds
                               defInit = findIdentifier i ds
                               defNext = findIdentifier n ds
                           in spec m cs vs defs defInit defNext

filename (Module m _) = snake m ++ ".ex"

{-- \vdash --}
-- (MOD)
spec :: Module -> [Constant] -> [Variable] -> [Definition] -> Init -> Next -> ElixirCode
spec m cs vs ds di dn = let g = map (\c -> (c, "const")) cs ++ map (\v -> (v, "variable")) vs
                            state = ini (g ++ moduleContext m) di
                        in concat [moduleHeader m,
                                   ident (concat [
                                             constants cs,
                                             mapAndJoin (definition g) ds,
                                             "\n",
                                             next g dn,
                                             decideAction
                                             ]
                                         ),
                                   "\nend\n\n",
                                   mainCall m state]

{-- \vdash_const --}
-- (CONST)
constants :: [Constant] -> ElixirCode
constants cs = unlines (map (\c -> let s = snake c
                                       decl = "@" ++ s ++ " \"<value for " ++ c ++ ">\"\n"
                                       acc = "def " ++ s ++ ", do: @" ++ s ++ "\n\n"
                                   in decl ++ acc) cs)

{-- \vdash_dec --}
-- (DEF)
definition :: Context -> Definition -> ElixirCode
definition g (ActionDefinition i ps doc a) = let g' = g ++ map (\p -> (p, "param")) ps
                                                 (conditions, actions) = actionsAndConditions g' a
                                             in if actions == []
                                                then declaration (i ++ "Condition") ps ++ ident (cFold conditions) ++ "\nend\n\n"
                                                else funDoc doc ++ declaration (i ++ "Condition") ps ++ ident (cFold conditions) ++ "\nend\n\n" ++ declaration i ps ++ ident (aFold actions) ++ "\nend\n\n"

definition g (ValueDefinition i v) = declaration i [] ++ ident (value g v) ++ "\nend\n\n"
-- Comment translation, not specified
definition _ (Comment s) = "# " ++ cleanTrailing s


{-- \vdash_d --}
actionsAndConditions :: Context -> Action -> ([ElixirCode], [ElixirCode])

-- (CALL)
actionsAndConditions g (ActionCall i ps) = ([call (i ++ "Condition") ("variables":map (value g) ps)], [call i ("variables":map (value g) ps)])

-- (AND)
actionsAndConditions g (ActionAnd as) = let (ics, ias) = unzipAndFold (map (actionsAndConditions g) as)
                                        in (if allUnchanged as then ["false"] else [cFold ics], ias)

-- (OR)
actionsAndConditions g (ActionOr as) = let (ics, ias) = unzipAndFold (map (actionsAndConditions g) as)
                                       in (if allUnchanged as then ["false"] else [orFold ics], if ias == [] then [] else [decide g as])

-- (IF)
actionsAndConditions g (If p t e) = let cp = predicate g p
                                        (ct, at) = actionsAndConditions g t
                                        (ce, ae) = actionsAndConditions g e
                                        c = ifExpr cp (if isUnchanged t then "false" else cFold ct) (if isUnchanged e then "false" else cFold ce)
                                        a = ifExpr cp (aFold at) (aFold ae)
                                    in ([c], [a])

-- (COND)
actionsAndConditions g (Condition p) = ([predicate g p], [])

-- [new] (EXT)
actionsAndConditions g (Exists i v (ActionOr as)) = let ig = (i, "param"):g
                                                        (ics, _) = unzipAndFold (map (actionsAndConditions ig) as)
                                                        c = "Enum.any?(" ++ value ig v ++ ", fn (" ++ i ++ ") ->" ++ orFold ics ++ "end\n)"
                                                    in ([c], [decide g [Exists i v (ActionOr as)]])
-- [new]: must test
actionsAndConditions g (ForAll i v (ActionAnd as)) = let ig = (i, "param"):g
                                                         (ics, ias) = unzipAndFold (map (actionsAndConditions ig) as)
                                                         c = "Enum.all?(" ++ value ig v ++ ", fn (" ++ i ++ ") ->" ++ cFold ics ++ "end\n)"
                                                     in ([c], ias)

-- (TRA)
actionsAndConditions g a = ([], [action g a])

decide :: Context -> [Action] -> ElixirCode
decide g [] = ""
decide g as = let infos = map (actionInfo g) as
                  list = "List.flatten([\n" ++ ident (intercalate ",\n" infos) ++ "\n])\n"
              in "(\n" ++ ident ("decide_action(\n" ++ ident list ++ "\n)\n") ++ "\n)"


{-- \vdash_a --}
action :: Context -> Action -> ElixirCode

-- (ACT-PRIM)
action g (Primed i v) = "%{ " ++ snake i ++ ": " ++ value g v ++ " }"

-- (ACT-UNCH)
action _ (Unchanged is) =  let u = \i -> snake i ++ ": variables[:" ++ snake i ++ "]"
                           in "%{ " ++ intercalate ",\n" (map u is) ++ " }"

-- [new] needs testing
action g (Value v) = value g v

action _ a = error(show a)
{-- \vdash_p --}
predicate :: Context -> Predicate -> ElixirCode

-- (PRED-EQ)
predicate g (Equality v1 v2) = value g v1 ++ " == " ++ value g v2

-- (PRED-INEQ)
predicate g (Inequality v1 v2) = value g v1 ++ " != " ++ value g v2

-- Similar rules
predicate g (Gt v1 v2) = value g v1 ++ " > " ++ value g v2
predicate g (Lt v1 v2) = value g v1 ++ " < " ++ value g v2
predicate g (Gte v1 v2) = value g v1 ++ " >= " ++ value g v2
predicate g (Lte v1 v2) = value g v1 ++ " <= " ++ value g v2

-- [new] (PRED-CALL)
predicate g (ConditionCall i ps) = call (i ++ "Condition") ("variables":map (value g) ps)

-- (PRED-IN)
predicate g (RecordBelonging v1 v2) = "Enum.member?(" ++ value g v2 ++ ", " ++ value g v1 ++ ")"

-- [new] (PRED-NOTIN)
predicate g (RecordNotBelonging v1 v2) = "not " ++ predicate g (RecordBelonging v1 v2)

-- (PRED-NOT)
predicate g (Not p) = "not " ++ predicate g p

-- [new] (PRED-AND)
predicate g (And ps) =  intercalate " and " (map (predicate g) ps)

-- [new] (PRED-OR)
predicate g (Or ps) =  intercalate " or " (map (predicate g) ps)

{-- \vdash_init --}
initialState :: Context -> Action -> ElixirCode

-- (INIT-AND)
initialState g (ActionAnd as) = aFold (map (initialState g) as)

-- (INIT-EQ)
initialState g (Condition (Equality (Arith (Ref i)) v)) = "%{ " ++ snake i ++ ": " ++ value g v ++ " }"

-- Restriction
initialState _ p = error("Init condition ambiguous: " ++ show p)

-- Comment extraction
ini g (ActionDefinition _ _ doc a) = comment doc ++ initialState g a


{-- \vdash_next --}
next :: Context -> Definition -> ElixirCode

-- (NEXT)
next g (ActionDefinition _ _ doc a) = let (_, actions) = actionsAndConditions g a
                                in funDoc doc ++ "def main(variables) do\n" ++ ident (logState ++ "main(" ++ (aFold actions)) ++ ")\nend\n"


{-- \vdash_i -}
actionInfo :: Context -> Action -> ElixirCode
-- (INFO-EX)
actionInfo g (Exists i v (ActionOr as)) = let ig = (i, "param"):g
                                              l = map (actionInfo ig) as
                                              s = intercalate ",\n" l
                                          in "Enum.map(" ++ value ig v ++ ", fn (" ++ i ++ ") -> [\n" ++ ident s ++ "\n] end\n)"

-- (INFO-DEF)
actionInfo g a = let (cs, as) = actionsAndConditions g a
                     n = "action: \"" ++ actionName a ++ "\""
                     c = "condition: " ++ cFold cs
                     s = "state: " ++ aFold as
                 in "%{ " ++ intercalate ", " [n,c,s] ++  " }"


{-- \vdash_v --}
value :: Context -> Value -> ElixirCode

-- (REC-INDEX)
value g (Index v k) = value g v ++ "[" ++ value g k ++ "]"

-- (SET-LIT)
value g (Set vs) = "MapSet.new([" ++ intercalate ", " (map (value g) vs) ++ "])"

-- (SET-UNION)
value g (Union (Set [v]) s) = "MapSet.put(" ++ value g s ++ ", " ++ value g v ++ ")"
value g (Union s (Set [v])) = "MapSet.put(" ++ value g s ++ ", " ++ value g v ++ ")"
value g (Union s1 s2) = "MapSet.union(" ++ value g s1 ++ ", " ++ value g s2 ++ ")"

-- [new] (SET-FILT)
value g (Filtered i v p) = "Enum.filter(" ++ value g v ++ ", fn(" ++ i ++ ") -> " ++ predicate ((i, "param"):g) p ++ " end)"

-- [new] (SET-CAR)
value g (Cardinality s) = "Enum.count(" ++ value g s ++ ")"

-- (REC-LIT) and (REC-EX), aggregated to ensure ordering
value g (Record rs) = let (literals, generations) = partition isLiteral rs
                          m = intercalate " ++ " (map (mapping g) generations) -- merge
                          l = "%{ " ++ intercalate ", " (map (mapping g) literals) ++ " }"
                      in if m == [] then l else m ++ " |> Enum.into(" ++ l ++ ")"

-- (REC-EXCEPT)
value g (Except i [(k, v)]) = "Map.put(" ++ reference g i ++ ", " ++ value g k ++ ", " ++ value g v ++ ")"

-- [new] (CASE)
value g (Case ms) = "cond do\n" ++ intercalate "\n" (map (caseMatch g) ms) ++ "\nend\n"

-- Others, not specified
value g (Arith e) = expression g e
value _ (Str s) = show s
value g (Range n1 n2) = expression g n1 ++ ".." ++ expression g n2
value _ (Boolean b) = if b then "true" else "false"

caseMatch g (Match p v) = predicate g p ++ " -> " ++ value g v
caseMatch g (DefaultMatch v) = "true -> " ++ value g v

mapping g ((Key i), v) = snake i ++ ": " ++ value g v
mapping g ((All i a), v) = let ig = (i, "param"):g
                           in value g a ++ " |> Enum.map(fn (" ++ i ++ ") -> {" ++ i ++ ", " ++ value ig v ++ "} end)"
-- (VAL-*)
reference g i = if elem (i, "param") g then i else 
                  if elem (i, "const") g then cnst g i else
                    if elem (i, "variable") g then "variables[:" ++ snake i ++ "]" else
                      i ++ "(variables)"

cnst g i = case dropWhile (\d ->snd d /= "module") g of
              [] -> "@" ++ snake i
              ms -> fst (head ms) ++ "." ++ snake i

-- Arithmetic expressions, from EXTEND INTEGERS
expression :: Context -> Value -> ElixirCode
expression _ (Num d) = show d
expression g (Ref i) = reference g i
expression g (Neg a) = "-" ++ expression' g a
expression g (Add a b) = expression' g a ++ " + " ++ expression' g b
expression g (Sub a b) = expression' g a ++ " - " ++ expression' g b
expression g (Mul a b) = expression' g a ++ " * " ++ expression' g b
expression g (Div a b) = expression' g a ++ " / " ++ expression' g b
expression g (Mod a b) = "rem(" ++ expression' g a ++ ", " ++ expression' g b ++ ")"

expression' _ (Num d) = show d
expression' g (Ref i) = reference g i
expression' g e = "(" ++ expression g e ++ ")"

