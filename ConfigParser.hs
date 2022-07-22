{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module ConfigParser where

import qualified Head as H
import Parser

import Data.Aeson
import qualified Data.ByteString.Lazy as B
import GHC.Generics

jsonFile :: FilePath
jsonFile = "config-sample.json"

data DistributionConfig =
  Config [ProcessConfig] [String]
  deriving (Show, Generic)

data ProcessConfig =
  PConfig String [H.Action]
  deriving (Show, Generic)

instance FromJSON DistributionConfig where
  parseJSON =
    withObject "DistribuitionConfig" $ \obj -> do
      ps <- obj .: "processes"
      vs <- obj .: "shared_variables"
      return (Config ps vs)

instance FromJSON ProcessConfig where
  parseJSON =
    withObject "ProcessConfig" $ \obj -> do
      i <- obj .: "process_id"
      as <- obj .: "actions"
      case mapM parseState as of
        Left e -> fail ("Invalid action in:" ++ show as ++ ". Error: " ++ show e)
        Right cs -> return (PConfig i cs)

parseConfig :: FilePath -> IO (Either String DistributionConfig)
parseConfig file = do
  content <- B.readFile file
  return (eitherDecode content)
-- main :: IO ()
-- main = parseJson jsonFile >>= print

processNames :: DistributionConfig -> [String]
processNames (Config ps _) = map (\(PConfig n _) -> n) ps
