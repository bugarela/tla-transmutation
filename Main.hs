import System.Environment

import           Elixir
import           Head
import           Parser (parseTla)
import           JSONParser (parseJson)
import           ConfigParser (parseConfig)
import Control.Applicative

convert mode init next config (m, ds) = let f = "elixir/lib/generated_code/" ++ filename m
                                        -- in writeFile f (generate (Spec m init next ds) config) >> return f
                                        in print (generate (Spec m init next ds) config) >> return f

main = do (mode:name:i:n:configFile:_) <- getArgs
          config <- parseConfig configFile
          ls <- if mode == "tla" then parseTla name else parseJson name
          case liftA2 (convert name i n) config ls of
            Left e -> putStrLn e
            Right f -> do a <- f
                          putStrLn ("Elixir file written to " ++ a)
