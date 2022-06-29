{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module ConfigParser where

import Data.Aeson
import GHC.Generics
import qualified Data.ByteString.Lazy as B

jsonFile :: FilePath
jsonFile = "config-sample.json"

data DistributionConfig = Config [ProcessConfig] [String] deriving (Show,Generic)

data ProcessConfig = PConfig String [String] deriving (Show,Generic)

instance FromJSON DistributionConfig where
    parseJSON = withObject "DistribuitionConfig" $ \obj -> do
      ps <- obj .: "processes"
      vs <- obj .: "shared_variables"
      return (Config ps vs)

instance FromJSON ProcessConfig where
    parseJSON = withObject "ProcessConfig" $ \obj -> do
      i <- obj .: "process_id"
      as <- obj .: "actions"
      return (PConfig i as)

parseConfig :: FilePath -> IO (Either String DistributionConfig)
parseConfig file = do content <- B.readFile file
                      return (eitherDecode content)

-- main :: IO ()
-- main = parseJson jsonFile >>= print
