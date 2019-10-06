import Parser

parse a = do ls <- parseFile a
             case ls of
                Left e -> print e
                Right ls -> print ls
             return ()
