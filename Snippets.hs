module Snippets where

decideAction =
  unlines
    [ ""
    , "def decide_action(oracle, actions, step) do"
    , "  possible_actions = Enum.filter(actions, fn(action) -> action[:condition] end)"
    , "  different_states = Enum.uniq_by(possible_actions, fn(action) -> action[:state] end)"
    , ""
    , "  cond do"
    , "    Enum.count(different_states) == 1 ->"
    , "      Enum.at(possible_actions, 0)[:state]"
    , "    Enum.empty?(different_states) ->"
    , "      IO.puts(\"DEADLOCK\")"
    , "      exit(0)"
    , "    true ->"
    , "      send oracle, {:choose, self(), possible_actions}"
    , ""
    , "      n = receive do"
    , "        {:ok, n} -> n"
    , "        {:stop} -> exit(0)"
    , "      end"
    , ""
    , "      Enum.at(possible_actions, n)[:state]"
    , "  end"
    , "end"
    ]

mainFunction =
  unlines
    [ "def main(oracle, private_variables, step) do"
    , "  shared_state = wait_lock(oracle)"
    , "  variables = Map.merge(private_variables, shared_state)"
    , ""
    , "  IO.puts(inspect(variables))"
    , "  actions = next(variables)"
    , ""
    , "  next_variables = decide_action(oracle, actions, step)"
    , "  send(oracle, {:notify, step, variables, next_variables})"
    , ""
    , "  main(oracle, next_variables, step + 1)"
    , "end"
    ]

waitLockFunction =
  unlines
    [ "def wait_lock(oracle) do"
    , "  send(oracle, {:lock, self()})"
    , "  receive do"
    , "    {:ok, state} -> Map.split(state, shared_variables)"
    , "    {:already_locked, _} -> Process.sleep(1000); wait_lock(oracle)"
    , "  end"
    , "end"
    ]

logState = "IO.puts (inspect variables)\n\n"

oracleDelaration = "require Oracle\n\n"
