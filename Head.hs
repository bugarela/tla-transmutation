module Head where

import Math

type Identifier = String
type Parameter = Identifier
type Constant = Identifier
type Documentation = [String]
type ElixirCode = String
type Init = Definition
type Next = Definition
type Context = [(Identifier, String)]

data Spec = Spec Module Identifier Identifier [Definition]

data Module = Module Identifier Documentation deriving(Show, Eq)

data Definition = Definition Identifier [Parameter] Documentation Action | Constants [Identifier] | Comment String deriving(Show, Eq)

data Key = Key Identifier | All Identifier Value deriving(Show, Eq)

data Predicate = Equality Value Value | Inequality Value Value
               | Gt Value Value | Lt Value Value
               | Gte Value Value | Lte Value Value
               | RecordBelonging Value Value
               | RecordNotBelonging Value Value
               | And [Predicate]
               | Or [Predicate]
               | ForAll Identifier Value Predicate
               | Not Predicate
               | ConditionCall Identifier [Parameter] deriving(Show, Eq)

data Action = Condition Predicate | Primed Identifier Value | Unchanged [Identifier] | ActionNot Action
            | ActionAnd [Action] | ActionOr [Action] | ActionCall Identifier [Parameter]
            | If Predicate Action Action | Exists Identifier Value Action deriving(Show, Eq)

data Value = Set [Value] | Union Value Value | Filtered Identifier Value Predicate | Cardinality Value
           | Record [(Key, Value)] | Except Identifier Identifier Value
           | Str String | Arith Expr | Index Value Value | Range Expr Expr deriving(Show, Eq)

