{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module JSONParser where

import Control.Applicative
import Control.Arrow
import Data.Aeson
import qualified Data.ByteString.Lazy as B
import GHC.Generics
import qualified Head as H

type Kind = String

jsonFile :: FilePath
jsonFile = "tla_specifications/TokenTransfer2.json"

data Spec =
  Spec [Module]
  deriving (Show, Generic)

data Module =
  Module String [Declaration]
  deriving (Show, Generic)

data Declaration
  = Declaration Kind String (Maybe [FormalParam]) (Maybe Expression)
  | Ignored
  deriving (Show, Generic)

data Expression
  = ValEx TlaValue
  | NameEx String
  | OperEx String [Expression]
  | LetInEx [Declaration] Expression
  deriving (Show, Generic)

data FormalParam =
  Param String
  deriving (Show, Generic)

data TlaValue
  = TlaStr String
  | TlaBool Bool
  | TlaInt Integer
  | FullSet String
  deriving (Show, Generic)

instance FromJSON Spec where
  parseJSON =
    withObject "Spec" $ \obj -> do
      ms <- obj .: "modules"
      return (Spec ms)

instance FromJSON Module where
  parseJSON =
    withObject "Module" $ \obj -> do
      ds <- obj .: "declarations"
      i <- obj .: "name"
      return (Module i ds)

instance FromJSON Declaration where
  parseJSON =
    withObject "Declaration" $ \obj -> do
      src <- obj .: "source"
      filename <-
        case src of
          Object a -> a .: "filename"
          _ -> return "UNKNOWN"
      case filename :: String of
        "Functions" -> return Ignored
        "SequencesExt" -> return Ignored
        "Apalache" -> return Ignored
        _ -> do
          k <- obj .: "kind"
          n <- obj .: "name"
          ps <- obj .:? "formalParams"
          b <- obj .:? "body"
          return (Declaration k n ps b)

instance FromJSON FormalParam where
  parseJSON =
    withObject "FormalParam" $ \obj -> do
      name <- obj .: "name"
      return (Param name)

instance FromJSON TlaValue where
  parseJSON =
    withObject "TlaValue" $ \obj -> do
      valueKind <- obj .: "kind"
      case valueKind of
        "TlaBool" -> fmap TlaBool (obj .: "value")
        "TlaStr" -> fmap TlaStr (obj .: "value")
        "TlaInt" -> fmap TlaInt (obj .: "value")
        "TlaIntSet" -> return (FullSet "Int")
        "TlaNatSet" -> return (FullSet "Nat")
        "TlaBoolSet" -> return (FullSet "Bool")
        _ -> fail ("Unknown value kind: " ++ valueKind)

instance FromJSON Expression where
  parseJSON =
    withObject "Expression" $ \obj -> do
      exprKind <- obj .: "kind"
      case exprKind :: String of
        "ValEx" -> fmap ValEx (obj .: "value")
        "NameEx" -> fmap NameEx (obj .: "name")
        "OperEx" -> liftA2 OperEx (obj .: "oper") (obj .: "args")
        "LetInEx" -> liftA2 LetInEx (obj .: "decls") (obj .: "body")
        _ -> fail ("Unknown expression kind: " ++ exprKind)

-- TODO: Parse this from config or something
actionNames :: [String]
-- actionNames = ["SendMsg", "Deactivate", "Environment", "System", "PassToken", "InitiateProbe", "Next"]
actionNames = ["SubmitTransfer", "CommitTransfer", "SubmitTransferFrom", "CommitTransferFrom", "SubmitApprove", "CommitApprove", "Next"]

notIgnored Ignored = False
notIgnored _ = True

convertSpec :: Spec -> Either String (H.Module, [H.Definition])
convertSpec (Spec [Module i ds]) = fmap (H.Module i [], ) (mapM convertDefinitions (filter notIgnored ds))

convertDefinitions :: Declaration -> Either String H.Definition
convertDefinitions (Declaration k n ps body) =
  case body of
    Just b -> convertBody k n ps b
    Nothing ->
      case k of
        "TlaConstDecl" -> Right (H.Constants [n])
        "TlaVarDecl" -> Right (H.Variables [n])
        "OperEx" -> Left "OperEx needs body"
        _ -> Left ("Unknown kind" ++ show k ++ " body " ++ show body)

convertBody :: Kind -> String -> Maybe [FormalParam] -> Expression -> Either String H.Definition
convertBody k i ps e =
  case k of
    "TlaOperDecl" ->
      if isTemporal e
        then Right (H.Comment (show i ++ ": " ++ show e))
        else if isPredicate e
          then convertValue e >>= \x -> Right (H.ValueDefinition i (convertParams ps) x)
          else convertExpression e >>= \x -> Right (H.ActionDefinition i (convertParams ps) [] x)
    "TlaAssumeDecl" -> Right (H.Comment (show e))
    _ -> Left ("Unknown body kind " ++ show k)

convertParams :: Maybe [FormalParam] -> [String]
convertParams (Just ps) = map (\(Param s) -> s) ps
convertParams Nothing = []

primed :: Expression -> Either String H.Identifier
primed (OperEx o [a]) =
  case o of
    "PRIME" -> identifier a
    _ -> Left ("Not prime operator: " ++ o)

identifier :: Expression -> Either String H.Identifier
identifier (NameEx i) = Right i
identifier e = Left ("Expected name expression when looking for identifier, got: " ++ show e)

manyIdentifiers :: Expression -> Either String [H.Identifier]
manyIdentifiers (NameEx i) = Right [i]
manyIdentifiers (OperEx o as) =
  case o of
    "TUPLE" -> mapM identifier as
    _ -> Left ("Not tuple operator: " ++ o)

val :: TlaValue -> H.Lit
val (TlaStr s) = H.Str s
val (TlaBool b) = H.Boolean b
val (TlaInt n) = H.Num n
val (FullSet s) = H.FullSet s

splits :: [a] -> [(a, a)]
splits [a, b] = [(a, b)]
splits (a:b:ts) = (a, b) : splits ts

convertValue :: Expression -> Either String H.Value
convertValue (NameEx i) = Right (H.Ref i)
convertValue (ValEx v) = Right (H.Lit (val v))
convertValue (OperEx o as) =
  let r =
        case o of
          "FUN_SET" ->
            case as of
              [a1, a2] -> liftA2 H.FunSet (convertValue a1) (convertValue a2)
          "FUN_APP" ->
            case as of
              [a1, a2] -> liftA2 H.Index (convertValue a1) (convertValue a2)
          "FUN_CTOR" ->
            case as of
              [a1, a2, a3] -> liftA3 H.FunGen (identifier a2) (convertValue a3) (convertValue a1)
          "SET_TIMES" ->
            case as of
              [a1, a2] -> liftA2 H.SetTimes (convertValue a1) (convertValue a2)
          "SET_ENUM" ->
            case as of
              vs -> fmap H.Set (mapM convertValue vs)
          "SET_IN" ->
            case as of
              [a1, a2] -> liftA2 H.SetIn (convertValue a1) (convertValue a2)
          "SET_MINUS" ->
            case as of
              [a1, a2] -> liftA2 H.SetMinus (convertValue a1) (convertValue a2)
          "SET_FILTER" ->
            case as of
              [a1, a2, a3] -> liftA3 H.Filtered (identifier a1) (convertValue a2) (convertValue a3)
          "SET_UNION2" ->
            case as of
              [a1, a2] -> liftA2 H.Union (convertValue a1) (convertValue a2)
          "Apalache!ApaFoldSet" ->
            case as of
              [a1, a2, a3] -> liftA3 H.Fold (convertValue a1) (convertValue a2) (convertValue a3)
          "INT_RANGE" ->
            case as of
              [a1, a2] -> liftA2 H.Range (convertValue a1) (convertValue a2)
          "TUPLE" ->
            case as of
              vs -> fmap H.TupleVal (mapM convertValue vs)
          "RECORD" ->
            case as of
              vs -> fmap H.Record (convertRecordValues vs)
          "RECORD_SET" ->
            case as of
              vs -> fmap H.RecordSet (convertRecordValues vs)
          "MINUS" ->
            case as of
              [a1, a2] -> liftA2 H.Sub (convertValue a1) (convertValue a2)
          "PLUS" ->
            case as of
              [a1, a2] -> liftA2 H.Add (convertValue a1) (convertValue a2)
          "MOD" ->
            case as of
              [a1, a2] -> liftA2 H.Mod (convertValue a1) (convertValue a2)
          "EXCEPT" ->
            case as of
              (e:es) -> liftA2 H.Except (identifier e) (fmap splits (mapM convertValue es))
          "DOMAIN" ->
            case as of
              [a1] -> fmap H.Domain (convertValue a1)
          "FiniteSets!Cardinality" ->
            case as of
              [a1] -> fmap H.Cardinality (convertValue a1)
          "NE" ->
            case as of
              [x1, x2] -> liftA2 H.Inequality (convertValue x1) (convertValue x2)
          "EQ" ->
            case as of
              [x1, x2] -> liftA2 H.Equality (convertValue x1) (convertValue x2)
          "GT" ->
            case as of
              [x1, x2] -> liftA2 H.Gt (convertValue x1) (convertValue x2)
          "LT" ->
            case as of
              [x1, x2] -> liftA2 H.Lt (convertValue x1) (convertValue x2)
          "GE" ->
            case as of
              [x1, x2] -> liftA2 H.Gte (convertValue x1) (convertValue x2)
          "LE" ->
            case as of
              [x1, x2] -> liftA2 H.Lte (convertValue x1) (convertValue x2)
          "EXISTS3" ->
            case as of
              [a1, a2, a3] -> liftA3 H.PExists (identifier a1) (convertValue a2) (convertValue a3)
          "FORALL3" ->
            case as of
              [a1, a2, a3] -> liftA3 H.PForAll (identifier a1) (convertValue a2) (convertValue a3)
          "AND" ->
            case as of
              es -> fmap H.And (mapM convertValue es)
          "OR" ->
            case as of
              es -> fmap H.Or (mapM convertValue es)
          "NOT" ->
            case as of
              [a] -> fmap H.Not (convertValue a)
          "IF_THEN_ELSE" ->
            case as of
              [a1, a2, a3] -> liftA3 H.If (convertValue a1) (convertValue a2) (convertValue a3)
          "OPER_APP" ->
            case as of
              (e:es) -> liftA2 H.ConditionCall (identifier e) (mapM convertValue es)
          op -> Left ("Unknown value operator " ++ op)
   in left (\s -> s ++ "\nwhen converting " ++ show (OperEx o as)) r
convertValue (LetInEx ds b) = liftA2 H.Let (mapM convertDefinitions ds) (convertValue b)

convertAction :: Expression -> Either String H.Action
convertAction (OperEx o as) =
  let r =
        case o of
          "EXISTS3" ->
            case as of
              [a1, a2, a3] -> liftA3 H.Exists (identifier a1) (convertValue a2) (convertExpression a3)
          "FORALL3" ->
            case as of
              [a1, a2, a3] -> liftA3 H.ForAll (identifier a1) (convertValue a2) (convertExpression a3)
          "UNCHANGED" ->
            case as of
              [a] -> fmap H.Unchanged (manyIdentifiers a)
          "AND" ->
            case as of
              es -> fmap H.ActionAnd (mapM convertExpression es)
          "OR" ->
            case as of
              es -> fmap H.ActionOr (mapM convertExpression es)
          "EQ" ->
            case as of
              [a1, a2] -> liftA2 H.Primed (primed a1) (convertValue a2)
          "OPER_APP" ->
            case as of
              (e:es) -> liftA2 H.ActionCall (identifier e) (mapM convertValue es)
          "IF_THEN_ELSE" ->
            case as of
              [a1, a2, a3] -> liftA3 H.ActionIf (convertValue a1) (convertAction a2) (convertAction a3)
          op -> Left ("Unknown action operator " ++ op ++ " with args " ++ show as)
   in left (\s -> s ++ "\nwhen converting " ++ show (OperEx o as)) r
convertAction (LetInEx ds b) = liftA2 H.ActionLet (mapM convertDefinitions ds) (convertAction b)

convertExpression :: Expression -> Either String H.Action
convertExpression (ValEx v) = convertValue (ValEx v) >>= \cv -> Right (H.Condition cv)
convertExpression e =
  if isPredicate e
    then convertValue e >>= \x -> Right (H.Condition x)
    else convertAction e

actionOperators :: [String]
actionOperators = ["PRIME", "UNCHANGED"]

temporalOperators :: [String]
temporalOperators = ["GLOBALLY", "STUTTER", "IMPLIES", "LEADS_TO"]

isPredicate :: Expression -> Bool
isPredicate (OperEx o as) =
  all isPredicate as && if o == "OPER_APP"
                          then case identifier (head as) of {Right i -> i `notElem` actionNames}
                          else o `notElem` actionOperators
isPredicate (LetInEx ds b) = all definitionIsPredicate ds && isPredicate b
isPredicate _ = True

definitionIsPredicate (Declaration k n ps (Just body)) = isPredicate body
definitionIsPredicate _ = True

isTemporal :: Expression -> Bool
isTemporal (OperEx o as) = o `elem` temporalOperators || any isTemporal as
isTemporal _ = False

convertRecordValues :: [Expression] -> Either String [(H.Key, H.Value)]
convertRecordValues [] = Right []
convertRecordValues (ValEx l:v:vs) = do
  e <- convertValue v
  rs <- convertRecordValues vs
  return ((H.Key (val l), e) : rs)

parseJson :: FilePath -> IO (Either String (H.Module, [H.Definition]))
parseJson file = do
  content <- B.readFile file
  return ((eitherDecode content :: Either String Spec) >>= convertSpec)
-- main :: IO ()
-- main = do
--  d <- eitherDecode <$> B.readFile jsonFile
--  case d of
--   Left err -> putStrLn err
--   Right ps -> case convertSpec ps of
--     Left err -> putStrLn ("Error: " ++ err ++ show ps)
--     Right a -> print a
