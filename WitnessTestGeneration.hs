import System.Environment
import Data.List
import Parser
import Elixir
import Helpers

testFile moduleName testTrace testName = unlines [
  "defmodule Mix.Tasks." ++ testName ++ " do",
  "  @moduledoc \"Runs blackblox testing using the oracle\"",
  "  @shortdoc \"Runs trace checking for a witness\"",
  "  use Mix.Task",
  "",
  "  @impl Mix.Task",
  "  def run(_) do",
  "    trace =  [",
  intercalate ",\n" testTrace,
  "    ]",
  "",
  "    oracle = spawn(TraceCheckerOracle, :start, [trace])",
  "    " ++ moduleName ++ ".main(oracle, Enum.at(trace, 0), 0)",
  "  end",
  "end"
  ]

main :: IO ()
main = do
  (file:moduleName:testName:_) <- getArgs
  f <- readFile file
  case parseTrace f of
    Right ss -> let content = testFile moduleName (map (initialState []) ss) testName
                    outFile = "elixir/lib/mix/tasks/" ++ snake testName ++ ".ex"
                in writeFile outFile content
    Left e -> print e
