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

data Spec =
  Spec Module Identifier Identifier [Definition]
  deriving (Show, Eq)

data Module =
  Module Identifier Documentation
  deriving (Show, Eq)

data Definition
  = ActionDefinition Identifier [Parameter] Documentation Action
  | ValueDefinition Identifier [Parameter] Value
  | Constants [Identifier]
  | Variables [Identifier]
  | Comment String
  deriving (Show, Eq)

data Lit
  = Str String
  | Boolean Bool
  | Num Integer
  | FullSet String
  | Tuple [Lit]
  deriving (Show, Eq)

data Key
  = Key Lit
  | All Identifier Value
  deriving (Show, Eq)

data CaseMatch
  = Match Value Value
  | DefaultMatch Value
  deriving (Show, Eq)

data Action
  = Condition Value
  | Primed Identifier Value
  | Unchanged [Identifier]
  | ActionNot Action
  | ActionAnd [Action]
  | ActionOr [Action]
  | ActionCall Identifier [Value]
  | ActionIf Value Action Action
  | ActionLet [Definition] Action
  | Exists Identifier Value Action
  | ForAll Identifier Value Action
  deriving (Show, Eq)

data Value
  = Equality Value Value
  | Inequality Value Value
  | Gt Value Value
  | Lt Value Value
  | Gte Value Value
  | Lte Value Value
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
  | TupleVal [Value]
  | FunSet Value Value
  | FunGen Identifier Value Value
  | SetTimes Value Value
  | SetIn Value Value
  | SetMinus Value Value
  | Union Value Value
  | Filtered Identifier Value Value
  | Cardinality Value
  | Fold Value Value Value
  | Record [(Key, Value)]
  | RecordSet [(Key, Value)]
  | Except Identifier [(Value, Value)]
  | Case [CaseMatch]
  | Domain Value
  | Index Value Value
  | Range Value Value
  | Ref String
  | Neg Value
  | Add Value Value
  | Sub Value Value
  | Mul Value Value
  | Div Value Value
  | Mod Value Value
  | Lit Lit
  deriving (Show, Eq)
