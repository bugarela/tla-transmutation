import Parser
import Elixir

parse a = do ls <- parseFile a
             case ls of
                Left e -> print e
                Right ls -> print ls
             return ()

elixir a = do ls <- parseFile a
              case ls of
                 Left e -> print e
                 Right ls -> putStrLn (generate ls)
              return ()

file a = do ls <- parseFile a
            case ls of
               Left e -> print e
               Right ls -> writeFile "out.exs" (generate ls)
            return ()

