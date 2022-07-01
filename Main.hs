import System.Environment

import           Elixir
import           Head
import           Helpers
import           Parser (parseTla)
import           JSONParser (parseJson)
import           ConfigParser (parseConfig)
import           Control.Applicative

filename p =  "elixir/lib/generated_code/" ++ snake p ++ ".ex"

writeCode m (p, code) = let f = filename p in writeFile f code >> return f

writeStarter (name, code) = let f = "elixir/lib/mix/tasks/" ++ snake name ++ "_starter.ex" in writeFile f code >> return f

convert name init next config (m, ds) = do files <- mapM (writeCode name) (generate (Spec m init next ds) config)
                                           starter <- writeStarter (generateStarter (Spec m init next ds))
                                           return (starter, files)

main = do (mode:name:i:n:configFile:_) <- getArgs
          config <- parseConfig configFile
          ls <- if mode == "tla" then parseTla name else parseJson name
          case liftA2 (convert name i n) config ls of
            Left e -> putStrLn e
            Right f -> do a <- f
                          putStrLn ("Elixirs files written to " ++ show a)
