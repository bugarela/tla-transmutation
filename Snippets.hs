module Snippets where

decideAction = unlines [
             "",
             "def decide_action(actions) do",
             "  possible_actions = Enum.filter(actions, fn(action) -> action[:condition] end)",
             "  different_states = Enum.uniq_by(possible_actions, fn(action) -> action[:state] end)",
             "",
             "  cond do",
             "    Enum.count(different_states) == 1 ->",
             "      Enum.at(possible_actions, 0)[:state]",
             "    Enum.empty?(different_states) ->",
             "      IO.puts(\"DEADLOCK\")",
             "      exit(0)",
             "    true ->",
             "      send oracle, {:choose, self(), possible_actions}",
             "",
             "      n = receive do",
             "        {:ok, n} -> n",
             "        {:stop} -> exit(0)",
             "      end",
             "",
             "      Enum.at(possible_actions, n)[:state]",
             "  end",
             "end"
             ]

mainFunction = unlines [
             "def main(oracle, variables, step) do",
             "  IO.puts(inspect(variables))",
             "",
             "  actions = next(variables)",
             "",
             "  next_variables = decide_action(oracle, actions, step)",
             "  send(oracle, {:notify, step, variables, next_variables})",
             "",
             "  main(oracle, next_variables, step + 1)",
             "end"
             ]

logState = "IO.puts (inspect variables)\n\n"

oracleDelaration = "require Oracle\n\n"

starterTask name init = unlines [
                      "defmodule Mix.Tasks.Startmodel do",
                      "  @moduledoc \"Printed when the user requests `mix help echo`\"",
                      "  @shortdoc \"Echoes arguments\"",
                      "  use Mix.Task",
                      "",
                      "  @impl Mix.Task",
                      "  def run(_) do",
                      "      initial_state = " ++ init,
                      "",
                      "    oracle = spawn(RandomOracle, :start, [])",
                      "    " ++ name ++ ".main(oracle, initial_state, 0)",
                      "  end",
                      "end"
                      ]

tracerStarterTask name trace = unlines [
                             "defmodule Mix.Tasks.Startmodel do",
                             "  @moduledoc \"Printed when the user requests `mix help echo`\"",
                             "  @shortdoc \"Echoes arguments\"",
                             "  use Mix.Task",
                             "",
                             "  @impl Mix.Task",
                             "  def run(_) do",
                             "    trace =  ["
                             ] ++ trace ++ unlines [
                             "    ]",
                             "",
                             "    oracle = spawn(TraceCheckerOracle, :start, [trace])",
                             "     " ++ name ++ ".main(oracle, Enum.at(trace, 0), 0)",
                             "  end",
                             "end"
                             ]
