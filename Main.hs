import System.Environment

import ConfigParser
import Control.Applicative
import Elixir
import Head
import Helpers
import JSONParser (parseJson)
import Parser

filename dest p = dest ++ "/lib/generated_code/" ++ snake p ++ ".ex"

writeCode dest m (p, code) =
  let f = filename dest p
   in writeFile f code >> return f

writeStarter dest (name, code) =
  let f = dest ++ "/lib/mix/tasks/" ++ snake name ++ "_starter.ex"
   in writeFile f code >> return f

convert name init next dest config (m, ds) = do
  files <- mapM (writeCode dest name) (generate (Spec m init next ds) config)
  starter <- mapM (writeStarter dest . generateStarter (Spec m init next ds)) (processNames config)
  return (starter, files)

main = do
  (configFile:_) <- getArgs
  config <- parseConfig configFile
  case config of
    Left e -> putStrLn e
    Right (Config _ _ _ i n _ mode file _ _ dest) -> do
      ls <-
        if mode == "tla"
          then parseTla file
          else parseJson file
      case liftA2 (convert file i n dest) config ls of
        Left e -> putStrLn e
        Right f -> do
          a <- f
          putStrLn ("Elixirs files written to " ++ show a)
