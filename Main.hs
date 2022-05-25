import System.Environment

import           Elixir
import           Head
import           Parser (parseTla)
import           JSONParser (parseJson)

convert mode a init next = do ls <- if mode == "tla" then parseTla a else parseJson a
                              case ls of
                                Left e -> putStrLn e >> return[]
                                Right (m, ds) -> let f = "elixir/lib/generated_code/" ++ filename m
                                                 in writeFile f (generate (Spec m init next ds)) >> return f

main = do (mode:name:i:n:_) <- getArgs
          f <- convert mode name i n
          putStrLn ("Elixir file written to " ++ f)
