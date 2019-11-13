module Elixir where

import Data.List

import Head
import Math
import Snippets
import DocHandler
import Helpers

generate :: Spec -> ElixirCode
generate (Spec m i n ds) = let defs = filter (not . (specialDef i n)) ds
                               cs = findConstants ds
                               defInit = findIdentifier i ds
                               defNext = findIdentifier n ds
                           in spec m cs defs defInit defNext

{-- \vdash --}
-- (MOD)
spec :: Module -> [Constant] -> [Definition] -> Init -> Next -> ElixirCode
spec m cs ds di dn = let g = map (\c -> (c, "const")) cs
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
definition g (Definition i ps doc a) = let g' = g ++ map (\p -> (p, "param")) ps
                                           (conditions, actions) = actionsAndConditions g' a
                                       in funDoc doc ++ declaration (i ++ "Condition") ps ++ ident (cFold conditions) ++ "\nend\n\n" ++ declaration i ps ++ ident (aFold actions) ++ "\nend\n\n"
-- Comment translation, not specified
definition _ (Comment s) = "# " ++ cleanTrailing s


{-- \vdash_d --}
actionsAndConditions :: Context -> Action -> ([ElixirCode], [ElixirCode])

-- (AND)
actionsAndConditions g (ActionAnd as) = unzipAndFold (map (actionsAndConditions g) as)

-- (CALL)
actionsAndConditions _ (ActionCall i ps) = ([call (i ++ "Condition") ("variables":ps)], [call i ("variables":ps)])

-- (OR)
actionsAndConditions g (ActionOr as) = ([], [decide g as])

-- (IF)
actionsAndConditions g (If p t e) = let cp = predicate g p
                                        (ct, at) = actionsAndConditions g t
                                        (ce, ae) = actionsAndConditions g e
                                        c = ifExpr cp (cFold ct) (cFold ce)
                                        a = ifExpr cp (aFold at) (aFold ae)
                                    in ([c], [a])

-- (COND)
actionsAndConditions g (Condition p) = ([predicate g p], [])

-- (ACT)
actionsAndConditions g a = ([], [action g a])

decide :: Context -> [Action] -> ElixirCode
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

-- (PRED-IN)
predicate g (RecordBelonging v1 v2) = "Enum.member?(" ++ value g v2 ++ ", " ++ value g v1 ++ ")"

-- (PRED-NOT)
predicate g (Not p) = "not " ++ predicate g p


{-- \vdash_init --}
initialState :: Context -> Action -> ElixirCode

-- (INIT-AND)
initialState g (ActionAnd as) = aFold (map (initialState g) as)

-- (INIT-EQ)
initialState g (Condition (Equality (Arith (Ref i)) v)) = "%{ " ++ snake i ++ ": " ++ value g v ++ " }"

-- Restriction
initialState _ p = error("Init condition ambiguous: " ++ show p)

-- Comment extraction
ini g (Definition _ _ doc a) = comment doc ++ initialState g a


{-- \vdash_next --}
next :: Context -> Definition -> ElixirCode

-- (NEXT)
next g (Definition _ _ doc a) = let (_, actions) = actionsAndConditions g a
                                in funDoc doc ++ "def main(variables) do\n" ++ ident (logState ++ "main" ++ (aFold actions)) ++ "\nend\n"


{-- \vdash_i -}
actionInfo :: Context -> Action -> ElixirCode
-- (INFO-EX)
actionInfo g (Exists i v (ActionOr as)) = let l = map (actionInfo g) as
                                              s = intercalate ",\n" l
                                          in "Enum.map(" ++ value g v ++ ", fn (" ++ i ++ ") -> [\n" ++ ident s ++ "\n] end\n)"

-- (INFO-DEF)
actionInfo g a = let (cs, as) = actionsAndConditions g a
                     n = "action: \"" ++ actionName a ++ "\""
                     c = "condition: " ++ cFold cs
                     s = "state: " ++ aFold as
                 in "%{ " ++ intercalate ", " [n,c,s] ++  " }"


{-- \vdash_v --}
value :: Context -> Value -> ElixirCode

-- (REC-INDEX)
value g (Index v k) = value g v ++ "[" ++ k ++ "]"

-- (SET-LIT)
value g (Set vs) = "MapSet.new([" ++ intercalate ", " (map (value g) vs) ++ "])"

-- (SET-UNION)
value g (Union (Set [v]) s) = "MapSet.put(" ++ value g s ++ ", " ++ value g v ++ ")"
value g (Union s (Set [v])) = "MapSet.put(" ++ value g s ++ ", " ++ value g v ++ ")"
value g (Union s1 s2) = "MapSet.union(" ++ value g s1 ++ ", " ++ value g s2 ++ ")"

-- (REC-LIT) and (REC-EX), aggregated to ensure ordering
value g (Record rs) = let (literals, generations) = partition isLiteral rs
                          m = intercalate " ++ " (map (mapping g) generations) -- merge
                          l = "%{ " ++ intercalate ", " (map (mapping g) literals) ++ " }"
                      in if m == [] then l else m ++ " |> Enum.into(" ++ l ++ ")"

-- (REC-EXCEPT)
value g (Except i k v) = "Map.put(" ++ reference g i ++ ", " ++ k ++ ", " ++ value g v ++ ")"

-- Others, not specified
value g (Arith e) = expression g e
value _ (Str s) = show s

mapping g ((Key i), v) = snake i ++ ": " ++ value g v
mapping g ((All i a), v) = value g a ++ " |> Enum.map(fn (" ++ i ++ ") -> {" ++ i ++ ", " ++ value g v ++ "} end)"
-- (VAL-*)
reference g i = if elem (i, "param") g then i else 
                  if elem (i, "const") g then cnst g i else
                    "variables[:" ++ snake i ++ "]"

cnst g i = case dropWhile (\d ->snd d /= "module") g of
              [] -> "@" ++ snake i
              ms -> fst (head ms) ++ "." ++ snake i

-- Arithmetic expressions, from EXTEND INTEGERS
expression :: Context -> Expr -> ElixirCode
expression _ (Num d) = show d
expression g (Ref i) = reference g i
expression g (Neg a) = "-" ++ expression' g a
expression g (Add a b) = expression' g a ++ " + " ++ expression' g b
expression g (Sub a b) = expression' g a ++ " - " ++ expression' g b
expression g (Mul a b) = expression' g a ++ " * " ++ expression' g b
expression g (Div a b) = expression' g a ++ " / " ++ expression' g b

expression' _ (Num d) = show d
expression' g (Ref i) = reference g i
expression' g e = "(" ++ expression g e ++ ")"



