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
                          Right ls -> putStrLn (generate (Spec ls init next))
                        return ()

file a init next = do ls <- parseFile a
                      case ls of
                        Left e -> print e
                        Right ls -> writeFile "out.exs" (generate (Spec ls init next))
                      return ()

