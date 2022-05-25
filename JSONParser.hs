{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module JSONParser where

import qualified Head as H
import Data.Aeson
import GHC.Generics
import qualified Data.ByteString.Lazy as B
import Control.Applicative

type Kind = String

jsonFile :: FilePath
jsonFile = "tla_specifications/TokenTransfer2.json"

data Spec = Spec [Module] deriving (Show,Generic)

data Module = Module String [Declaration] deriving (Show, Generic)

data Declaration = Declaration Kind String (Maybe Expression) deriving (Show, Generic)
data Expression = Expression Kind (Maybe String) (Maybe [Expression]) (Maybe String) (Maybe TlaValue) deriving (Show, Generic)
data TlaValue = TlaStr String | TlaBool Bool | TlaInt Integer | FullSet String deriving (Show, Generic)

instance FromJSON Spec where
    parseJSON = withObject "Spec" $ \obj -> do
      ms <- obj .: "modules"
      return (Spec ms)

instance FromJSON Module where
    parseJSON = withObject "Module" $ \obj -> do
      ds <- obj .: "declarations"
      i <- obj .: "name"
      return (Module i ds)

instance FromJSON Declaration where
  parseJSON = withObject "Declaration" $ \obj -> do
      k <- obj .: "kind"
      n <- obj .: "name"
      b <- obj .:? "body"
      return (Declaration k n b)

instance FromJSON TlaValue where
    parseJSON = withObject "TlaValue" $ \obj -> do
      valueKind <- obj .: "kind"
      case valueKind of
        "TlaBool"           -> fmap TlaBool (obj .: "value")
        "TlaStr"            -> fmap TlaStr (obj .: "value")
        "TlaInt"            -> fmap TlaInt (obj .: "value")
        "TlaIntSet"         -> return (FullSet "Int")
        "TlaNatSet"         -> return (FullSet "Nat")
        _                   -> fail ("Unknown value kind: " ++ valueKind)

instance FromJSON Expression where
  parseJSON = withObject "Expression" $ \obj -> Expression <$> obj .:  "kind"
                                                           <*> obj .:? "oper"
                                                           <*> obj .:? "args"
                                                           <*> obj .:? "name"
                                                           <*> obj .:? "value"

convertSpec :: Spec -> Either String (H.Module, [H.Definition])
convertSpec (Spec [Module i ds]) = fmap (H.Module i [],) (mapM convertDefinitions ds)

convertDefinitions :: Declaration -> Either String H.Definition
convertDefinitions (Declaration k n body) = case body of
                                              Just b -> convertBody k n b
                                              Nothing -> case k of
                                                "TlaConstDecl" -> Right (H.Constants [n])
                                                "TlaVarDecl" -> Right (H.Variables [n])
                                                "OperEx" -> Left "OperEx needs body"
                                                _ -> Left ("Unknown kind" ++ show k ++ " body " ++ show body)

convertBody :: Kind -> String -> Expression -> Either String H.Definition
convertBody k i e = case k of
                      "OperEx" -> Right (H.Comment "A")
                      "TlaOperDecl" -> convertExpression e >>= \x -> Right (H.ActionDefinition i [] [] x)
                      _ -> Left ("Unknown body kind " ++ show k)


primed :: Expression -> Either String H.Identifier
primed (Expression k o as i v) = case o of
                                   Just "PRIME" -> case as of
                                                     Just [a] -> identifier a
                                   Nothing -> Left "Missing name in NameEx"

identifier :: Expression -> Either String H.Identifier
identifier (Expression k o as i v) = if k == "NameEx" then case i of
                                                        Just s -> Right s
                                                        Nothing -> Left "Missing name in NameEx"
                                                      else Left "Missing identifier"
ref :: Maybe String -> Either String H.Value
ref (Just v) = Right (H.Ref v)
ref x = Left ("Not a reference: " ++ show x)

val :: Maybe TlaValue -> Either String H.Value
val (Just(TlaStr s)) = Right (H.Str s)
val (Just(TlaBool b)) = Right (H.Boolean b)
val (Just(TlaInt n)) = Right (H.Num n)
val (Just (FullSet s)) = Right (H.FullSet s)
val Nothing = Left "Value not found"

splits :: [a] -> [(a, a)]
splits [a, b] = [(a, b)]
splits (a:b:ts) = (a,b):splits ts

convertValue :: Expression -> Either String H.Value
convertValue (Expression k o as i v) = case k of
                                         "NameEx" -> ref i
                                         "ValEx" -> val v
                                         "OperEx" -> case o of
                                           Just "FUN_SET" -> case as of
                                             Just [a1, a2] -> liftA2 H.FunSet (convertValue a1) (convertValue a2)
                                           Just "FUN_APP" -> case as of
                                             Just [a1, a2] -> liftA2 H.Index (convertValue a1) (convertValue a2)
                                           Just "SET_TIMES" -> case as of
                                             Just [a1, a2] -> liftA2 H.SetTimes (convertValue a1) (convertValue a2)
                                           Just "TUPLE" -> case as of
                                             Just vs -> fmap H.Tuple (mapM convertValue vs)
                                           Just "MINUS" -> case as of
                                             Just [a1, a2] -> liftA2 H.Sub (convertValue a1) (convertValue a2)
                                           Just "PLUS" -> case as of
                                             Just [a1, a2] -> liftA2 H.Add (convertValue a1) (convertValue a2)
                                           Just "EXCEPT" -> case as of
                                             Just (e:es) -> liftA2 H.Except (identifier e) (fmap splits (mapM convertValue es))
                                           Just "DOMAIN" -> case as of
                                             Just [a1] -> fmap H.Domain (convertValue a1)
                                           Just op -> Left ("Unknown value operator " ++ op)
                                         _ -> Left ("Unknown value kind " ++ k)

actionOperators :: [String]
actionOperators = ["PRIME", "UNCHANGED"]

convertPredicate :: Expression -> Either String H.Predicate
convertPredicate (Expression k o as i v) = case k of
                                             "OperEx" -> case o of
                                               Just "NE" -> case as of
                                                 Just [x1, x2] -> liftA2 H.Inequality (convertValue x1) (convertValue x2)
                                               Just "EQ" -> case as of
                                                 Just [x1, x2] -> liftA2 H.Equality (convertValue x1) (convertValue x2)
                                               Just "GT" -> case as of
                                                 Just [x1, x2] -> liftA2 H.Gt (convertValue x1) (convertValue x2)
                                               Just "GE" -> case as of
                                                 Just [x1, x2] -> liftA2 H.Gte (convertValue x1) (convertValue x2)
                                               Just "EXISTS3" -> case as of
                                                 Just [a1, a2, a3] -> liftA3 H.PExists (identifier a1) (convertValue a2) (convertPredicate a3)
                                               Just "FORALL3" -> case as of
                                                 Just [a1, a2, a3] -> liftA3 H.PForAll (identifier a1) (convertValue a2) (convertPredicate a3)
                                               Just "AND" -> case as of
                                                 Just es -> fmap H.And (mapM convertPredicate es)
                                               Just "OPER_APP" -> case as of
                                                 Just (e:es) -> liftA2 H.ConditionCall (identifier e) (mapM convertValue es)
                                               _ -> Left ("Unknown predicate operator " ++ show o)
                                             _ -> Left("Unknown predicate kind " ++ k)

convertAction :: Expression -> Either String H.Action
convertAction (Expression k o as i v) = case k of
                                          "OperEx" -> case o of
                                            Just "EXISTS3" -> case as of
                                              Just [a1, a2, a3] -> liftA3 H.Exists (identifier a1) (convertValue a2) (convertExpression a3)
                                            Just "FORALL3" -> case as of
                                              Just [a1, a2, a3] -> liftA3 H.ForAll (identifier a1) (convertValue a2) (convertExpression a3)
                                            Just "UNCHANGED" -> case as of
                                              Just es -> fmap H.Unchanged (mapM identifier es)
                                            Just "AND" -> case as of
                                              Just es -> fmap H.ActionAnd (mapM convertExpression es)
                                            Just "EQ" -> case as of
                                              Just [a1, a2] -> liftA2 H.Primed (primed a1) (convertValue a2)
                                            Just op -> Left("Unknown action operator " ++ op)
                                          _ -> Left("Unknown action kind " ++ k)

convertExpression :: Expression -> Either String H.Action
convertExpression (Expression k o as i v) = case k of
                                              "OperEx" -> case o of
                                                    Just x -> if isPredicate (Expression k o as i v) then convertPredicate (Expression k o as i v) >>= \x -> Right(H.Condition x) else convertAction (Expression k o as i v)
                                                    Nothing -> Left "Operator required"
                                              "ValEx" -> convertValue (Expression k o as i v) >>= \cv -> Right(H.Value cv)
                                              _ -> Left ("Unknown expresion type: " ++ k)

isPredicate :: Expression -> Bool
isPredicate (Expression k o as i v) = case o of
                                        Just x -> if x `elem` actionOperators
                                                  then False
                                                  else case as of
                                                         Just es -> all isPredicate es
                                                         Nothing -> True
                                        Nothing -> True

parseJson :: FilePath -> IO (Either String (H.Module, [H.Definition]))
parseJson file = do content <- B.readFile file
                    return ((eitherDecode content :: Either String Spec) >>= convertSpec)

-- main :: IO ()
-- main = do
--  d <- eitherDecode <$> B.readFile jsonFile
--  case d of
--   Left err -> putStrLn err
--   Right ps -> case convertSpec ps of
--     Left err -> putStrLn ("Error: " ++ err ++ show ps)
--     Right a -> print a
