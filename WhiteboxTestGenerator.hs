{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

import Data.Aeson
import qualified Data.ByteString.Lazy as B
import Data.List
import GHC.Generics
import System.Environment

import Head as H
import Elixir
import Helpers
import Parser
import ConfigParser

getJSON :: FilePath -> IO B.ByteString
getJSON = B.readFile

data Graph =
  Graph
    { nodes :: [Node]
    , edges :: [Edge]
    }
  deriving (Show, Generic)

data Node =
  Node
    { nodeId :: Integer
    , label :: String
    }
  deriving (Show, Generic)

data Edge =
  Edge
    { nodeFrom :: Integer
    , nodeTo :: Integer
    }
  deriving (Show, Generic)

instance FromJSON Graph where
  parseJSON (Object v) = Graph <$> v .: "objects" <*> v .: "edges"

instance FromJSON Node where
  parseJSON (Object v) = Node <$> v .: "_gvid" <*> v .: "label"

instance FromJSON Edge where
  parseJSON (Object v) = Edge <$> v .: "tail" <*> v .: "head"

genTests :: String -> [String] -> Graph -> Either String String
genTests m ms Graph {nodes = ns, edges = es} =
  case traverse (testForNode (map ((m ++ "_") ++) ms) (Graph ns es)) ns of
    Right ts -> Right (header m ++ intercalate "\n" ts ++ "\nend")
    Left e -> Left e

testForNode :: [String] -> Graph -> Node -> Either String String
testForNode ms g Node {nodeId = i, label = l} = do
  vs <- toMap Node {nodeId = i, label = l}
  ss <- statesFromId g i >>= traverse toMap
  return
    (unlines
       [ "test \"fromState " ++ show i ++ "\" do"
       , "  variables = " ++ vs
       , ""
       , "  expectedStates = [" ++ intercalate ",\n" ss ++ "]"
       , ""
       , "  actions = List.flatten([" ++ intercalate ", " (map (++ ".next(variables)") ms) ++ "])"
       , "  states = Enum.map(actions, fn action -> action[:transition].(variables) end)"
       , ""
       , "  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))"
       , "end"
       ])

statesFromId :: Graph -> Integer -> Either String [Node]
statesFromId Graph {nodes = ns, edges = es} i =
  let edgesFromId = filter (\Edge {nodeFrom = f, nodeTo = _} -> f == i) es
      nodesIdsFromId = map (\Edge {nodeFrom = _, nodeTo = t} -> t) edgesFromId
   in traverse (findNode ns) nodesIdsFromId

findNode :: [Node] -> Integer -> Either String Node
findNode ns n =
  case find (\Node {nodeId = i, label = _} -> n == i) ns of
    Just node -> Right node
    Nothing -> Left ("Node with id " ++ show n ++ " could not be found")

toMap :: Node -> Either String String
toMap Node {nodeId = _, label = l} =
  case parseState (unescape l) of
    Right a -> Right (initialState [] (toValue a))
    Left e -> Left (show e)


unescape :: String -> String
unescape [] = []
unescape [s] = [s]
unescape (c1:c2:cs) =
  if c1 == '\\' && (c2 == '\\' || c2 == 'n')
    then (if c2 == 'n'
            then unescape cs
            else unescape (c2 : cs))
    else c1 : unescape (c2 : cs)

header :: String -> String
header m = unlines ["defmodule " ++ m ++ "Test do", "  use ExUnit.Case", "  doctest " ++ m]

generateWhiteboxTests ps (Config _ _ _ _ _ name _ _ file _ dest) = do
  d <- (eitherDecode <$> getJSON file) :: IO (Either String Graph)
  case d of
    Left err -> putStrLn err
    Right graph -> case genTests name ps graph of
                     Left err -> putStrLn err
                     Right s ->
                       let f = dest ++ "/test/generated_code/" ++ snake name ++ "_test.exs"
                        in writeFile f s


main :: IO ()
main = do
  (configFile:_) <- getArgs
  config <- parseConfig configFile
  case fmap (\c -> generateWhiteboxTests (processNames c) c) config of
        Left err -> error err
        Right c -> c
