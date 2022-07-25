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

main :: IO ()
main = do
  (moduleName:file:testName:configFile:_) <- getArgs
  f <- readFile file
  config <- parseConfig configFile
  case fmap processNames config of
        Left err -> putStrLn err
        Right ms -> case parseTrace f of
                      Right ss ->
                        let content = testFile (map (initialState [] . toValue) ss) (map ((moduleName ++ "_") ++) ms) testName
                            outFile = "elixir/lib/mix/tasks/" ++ snake testName ++ ".ex"
                         in writeFile outFile content
                      Left e -> print e
