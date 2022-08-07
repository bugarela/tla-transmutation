import System.Environment

import ConfigParser (parseConfig, processNames)
import Control.Applicative
import Elixir
import Head
import Helpers
import JSONParser (parseJson)
import Parser

filename p = "elixir/lib/generated_code/" ++ snake p ++ ".ex"

writeCode m (p, code) =
  let f = filename p
   in writeFile f code >> return f

writeStarter (name, code) =
  let f = "elixir/lib/mix/tasks/" ++ snake name ++ "_starter.ex"
   in writeFile f code >> return f

convert name init next config (m, ds) = do
  files <- mapM (writeCode name) (generate (Spec m init next ds) config)
  starter <- mapM (writeStarter . generateStarter (Spec m init next ds)) (processNames config)
  return (starter, files)

main = do
  (mode:name:i:n:configFile:_) <- getArgs
  config <- parseConfig configFile
  ls <-
    if mode == "tla"
      then parseTla name
      else parseJson name
  case liftA2 (convert name i n) config ls of
    Left e -> putStrLn e
    Right f -> do
      a <- f
      putStrLn ("Elixirs files written to " ++ show a)
