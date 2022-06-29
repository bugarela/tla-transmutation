import System.Environment

import           Elixir
import           Head
import           Parser (parseTla)
import           JSONParser (parseJson)
import           ConfigParser (parseConfig)

convert mode init next config ls = do case ls of
                                        Left e -> putStrLn e >> return[]
                                        Right (m, ds) -> let f = "elixir/lib/generated_code/" ++ filename m
                                                         in writeFile f (generate (Spec m init next ds)) >> return f

main = do (mode:name:i:n:configFile:_) <- getArgs
          config <- parseConfig configFile
          ls <- if mode == "tla" then parseTla name else parseJson name
          f <- convert name i n config ls
          putStrLn ("Elixir file written to " ++ f)
