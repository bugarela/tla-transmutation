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
                        Left e -> print e
                        Right (m, ds) -> writeFile "elixir/lib/elixir.ex" (generate (Spec m init next ds))
                      return ()

