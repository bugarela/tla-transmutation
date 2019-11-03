module Head where

type Identifier = String
type Parameter = Identifier
type Documentation = [String]

data Spec = Spec Module Identifier Identifier

data Module = Module Header [Definition] deriving(Show)

data Header = Header Identifier Documentation deriving(Show)

data Definition = Definition Identifier [Parameter] Documentation Action | Comment String deriving(Show)

data Set = Set [Value] | Ref Identifier | Union Set Set deriving(Show)

data Literal = Str String | Numb Double  deriving(Show)

data Value = Variable Identifier | Constant Identifier | SetValue Set | RecordValue Record | LiteralValue Literal | Index Identifier Identifier deriving(Show)

data Key = Key Identifier | All Identifier Value deriving(Show)

data Record = Record [(Key, Value)] | Except Identifier Identifier Value deriving(Show)

data Predicate = Equality Value Value | Inequality Value Value | RecordBelonging Value Value deriving(Show)

data Action = Condition Predicate | Primed Identifier Value | Unchanged [Identifier] | ActionNot Action | ActionAnd [Action] | ActionOr [Action] | ActionCall Identifier [Parameter] deriving(Show)
