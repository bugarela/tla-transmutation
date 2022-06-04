module Head where

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

data CaseMatch = Match Value Value | DefaultMatch Value deriving(Show, Eq)

data Action = Condition Value
            | Primed Identifier Value
            | Unchanged [Identifier]
            | ActionNot Action
            | ActionAnd [Action]
            | ActionOr [Action]
            | ActionCall Identifier [Value]
            | ActionIf Value Action Action
            | Exists Identifier Value Action
            | ForAll Identifier Value Action
            deriving(Show, Eq)

data Value = Equality Value Value
           | Inequality Value Value
           | Gt Value Value | Lt Value Value
           | Gte Value Value | Lte Value Value
           | RecordBelonging Value Value
           | RecordNotBelonging Value Value
           | And [Value]
           | Or [Value]
           | Not Value
           | If Value Value Value
           | ConditionCall Identifier [Value]
           | PExists Identifier Value Value
           | PForAll Identifier Value Value
           | Let [Definition] Value
           | Set [Value]
           | Tuple [Value]
           | FunSet Value Value
           | FunGen Identifier Value Value
           | SetTimes Value Value
           | Union Value Value
           | Filtered Identifier Value Value
           | Cardinality Value
           | Record [(Key, Value)]
           | Except Identifier [(Value, Value)]
           | Case [CaseMatch]
           | Domain Value
           | Str String
           | Boolean Bool
           | FullSet String
           | Index Value Value
           | Range Value Value
           | Num Integer
           | Ref String
           | Neg Value
           | Add Value Value
           | Sub Value Value
           | Mul Value Value
           | Div Value Value
           | Mod Value Value
           deriving (Show, Eq)
