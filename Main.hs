import Head
import Parser
import Elixir

parse a = do ls <- parseFile a
             case ls of
                Left e -> print e
                Right ls -> print ls
             return ()

elixir a init next = do ls <- parseFile a
                        case ls of
                          Left e -> print e
                          Right (m, ds) -> putStrLn (generate (Spec m init next ds))
                        return ()

file a init next = do ls <- parseFile a
                      case ls of
                        Left e -> print e >> return([])
                        Right (m, ds) -> let f = "elixir/lib/generated_code/" ++ filename m
                                         in writeFile f (generate (Spec m init next ds)) >> return(f)

main = do putStrLn "TLA spec path:"
          tla <- getLine
          putStrLn "Initial state definition:"
          i <- getLine
          putStrLn "Next state function definition:"
          n <- getLine
          f <- file tla i n
          putStrLn ("Elixir file written to " ++ f)
