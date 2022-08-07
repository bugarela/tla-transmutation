import Data.List
import Elixir
import Helpers
import Parser
import System.Environment
import ConfigParser

testFile testTrace modules testName =
  unlines
    [ "defmodule Mix.Tasks." ++ testName ++ " do"
    , "  @moduledoc \"Runs blackblox testing using the oracle\""
    , "  @shortdoc \"Runs trace checking for a witness\""
    , "  use Mix.Task"
    , ""
    , "  @impl Mix.Task"
    , "  def run(_) do"
    , "    trace =  ["
    , intercalate ",\n" testTrace
    , "    ]"
    , ""
    , "    modules =  ["
    , "        " ++ intercalate ",\n      " modules
    , "    ]"
    , "    pids = Enum.map(modules, fn m -> spawn(m, :main, [self(), Enum.at(trace, 0), 0]) end)"
    , "    TraceCheckerOracle.start(trace, 0, nil, pids)"
    , "  end"
    , "end"
    ]

generateTestFromTrace moduleName dest ps (Test n t) = do
  f <- readFile t
  case parseTrace f of
    Right ss ->
      let content = testFile (map (initialState [] . toValue) ss) (map ((moduleName ++ "_") ++) ps) n
          outFile = dest ++ "/lib/mix/tasks/" ++ snake n ++ ".ex"
       in writeFile outFile content
    Left e -> print e

-- generateBlackboxTests :: [String] -> DistributionConfig -> Either String IO()
generateBlackboxTests ps (Config _ _ _ _ _ name _ _ _ tests dest) = mapM (generateTestFromTrace name dest ps) tests

main :: IO [()]
main = do
  (configFile:_) <- getArgs
  config <- parseConfig configFile
  case fmap (\c -> generateBlackboxTests (processNames c) c) config of
        Left err -> error err
        Right c -> c
