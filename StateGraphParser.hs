{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

import Data.Aeson
import Data.List
import GHC.Generics
import qualified Data.ByteString.Lazy as B

import Parser
import Elixir

jsonFile :: FilePath
jsonFile = "tla_specifications/states.json"

getJSON :: IO B.ByteString
getJSON = B.readFile jsonFile

data Graph = Graph { nodes :: [Node], edges :: [Edge] } deriving (Show, Generic)
data Node = Node { nodeId :: Integer, label :: String } deriving (Show, Generic)
data Edge = Edge { nodeFrom :: Integer, nodeTo :: Integer } deriving (Show, Generic)

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


genTests :: Graph -> Either String String
genTests Graph{nodes=ns, edges=es} = case traverse (testForNode (Graph ns es)) ns of
                                         Right ts -> Right (intercalate "\n" ts)
                                         Left e -> Left e

testForNode :: Graph -> Node -> Either String String
testForNode g Node{nodeId=i, label=l} = do vs <- toMap Node{nodeId=i, label=l}
                                           ss <- statesFromId g i >>= traverse toMap
                                           return ("variables = " ++ vs ++ "\n expectedStates = [" ++ intercalate "\n" ss ++ "]")

statesFromId :: Graph -> Integer -> Either String [Node]
statesFromId Graph{nodes=ns, edges=es} i = let edgesFromId = filter (\Edge{nodeFrom=f, nodeTo=_} -> f == i) es
                                               nodesIdsFromId = map (\Edge{nodeFrom=_, nodeTo=t} -> t) edgesFromId
                                            in traverse (findNode ns) nodesIdsFromId

findNode :: [Node] -> Integer -> Either String Node
findNode ns n = case find (\Node{nodeId=i, label=_} -> n == i) ns of
                  Just node -> Right node
                  Nothing -> Left ("Node with id " ++ show n ++ " could not be found")

toMap :: Node -> Either String String
toMap Node{nodeId=_, label=l} = case parseState (unescape l) of
                                  Right a -> Right (initialState [] a)
                                  Left e -> Left (show e)

unescape :: String -> String
unescape [] = []
unescape [s] = [s]
unescape(c1:c2:cs) = if c1 == '\\' && (c2 == '\\' || c2 == 'n') then (if c2 == 'n' then unescape cs else unescape (c2:cs)) else c1:unescape (c2:cs)

main :: IO ()
main = do
 d <- (eitherDecode <$> getJSON) :: IO (Either String Graph)
 case d of
  Left err -> putStrLn err
  Right ps -> case genTests ps of
    Left err -> putStrLn err
    Right s -> putStrLn s
