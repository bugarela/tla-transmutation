module Head where

import Math

type Identifier = String
type Parameter = Identifier
type Constant = Identifier
type Variable = Identifier
type Documentation = [String]
type ElixirCode = String
type Init = Definition
type Next = Definition
type Context = [(Identifier, String)]

data Spec = Spec Module Identifier Identifier [Definition] deriving(Show, Eq)

data Module = Module Identifier Documentation deriving(Show, Eq)

data Definition = ActionDefinition Identifier [Parameter] Documentation Action
                | ValueDefinition Identifier Value
                | Constants [Identifier]
                | Variables [Identifier]
                | Comment String
                deriving(Show, Eq)

data Key = Key Identifier | All Identifier Value deriving(Show, Eq)

data CaseMatch = Match Predicate Value | DefaultMatch Value deriving(Show, Eq)

data Predicate = Equality Value Value | Inequality Value Value
               | Gt Value Value | Lt Value Value
               | Gte Value Value | Lte Value Value
               | RecordBelonging Value Value
               | RecordNotBelonging Value Value
               | And [Predicate]
               | Or [Predicate]
               | Not Predicate
               | ConditionCall Identifier [Value]
               | PExists Identifier Value Predicate
               | PForAll Identifier Value Predicate
               deriving(Show, Eq)

data Action = Condition Predicate | Value Value | Primed Identifier Value | Unchanged [Identifier] | ActionNot Action
            | ActionAnd [Action] | ActionOr [Action] | ActionCall Identifier [Value]
            | If Predicate Action Action | Exists Identifier Value Action | ForAll Identifier Value Action deriving(Show, Eq)

data Value = Set [Value] | Tuple [Value] | FunSet Value Value | SetTimes Value Value | Union Value Value | Filtered Identifier Value Predicate | Cardinality Value
           | Record [(Key, Value)] | Except Identifier [(Value, Value)] | Case [CaseMatch] | Domain Value
           | Str String | Boolean Bool | FullSet String | Arith Expr | Index Value Value | Range Expr Expr
           | Num Integer
           | Ref String
           | Neg Value
           | Add Value Value
           | Sub Value Value
           | Mul Value Value
           | Div Value Value
           | Mod Value Value
           deriving (Show, Eq)
