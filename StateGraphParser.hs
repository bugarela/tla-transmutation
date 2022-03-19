{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

import qualified Head as H
import qualified Math as H
import Data.Aeson
import Data.List
import GHC.Generics
import qualified Data.ByteString.Lazy as B
import Control.Monad
import Control.Applicative
import Control.Monad.Instances

import Parser

jsonFile :: FilePath
jsonFile = "tla_specifications/states.json"

getJSON :: IO B.ByteString
getJSON = B.readFile jsonFile

data Graph = Graph { nodes :: [Node], edges :: [Edge] } deriving (Show,Generic)
data Node = Node { nodeId :: Integer, label :: String } deriving (Show,Generic)
data Edge = Edge { nodeFrom :: Integer, nodeTo:: Integer } deriving (Show,Generic)

instance FromJSON Graph where
   parseJSON (Object v) =
    Graph <$> v .: "objects"
          <*> v .: "edges"

instance FromJSON Node where
   parseJSON (Object v) =
    Node <$> v .: "_gvid"
         <*> v .: "label"

instance FromJSON Edge where
   parseJSON (Object v) =
    Edge <$> v .: "tail"
         <*> v .: "head"


genTests :: Graph -> String
genTests (Graph{nodes=ns, edges=es}) = let ts = map (testForNode es ns) ns in intercalate "\n" ts

testForNode es ns (Node{nodeId=id, label=l}) = let ss = statesFromId es ns id
  in "variables = " ++ l ++ "\n expectedStates = [" ++ intercalate "\n" ss ++ "]"

statesFromId :: [Edge] -> [Node] -> Integer -> [String]
statesFromId es ns i = map (\Edge{nodeFrom=_, nodeTo=t} -> show (findNode ns t)) (filter (\Edge{nodeFrom=f, nodeTo=t} -> f == i) es)

findNode :: [Node] -> Integer -> Maybe Node
findNode ns n = find (\Node{nodeId=id, label=_} -> n == id) ns

main :: IO ()
main = do
 d <- (eitherDecode <$> getJSON) :: IO (Either String Graph)
 case d of
  Left err -> putStrLn err
  Right ps -> putStrLn (genTests ps)
