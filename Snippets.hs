module Snippets where

decideAction =
  unlines
    [ ""
    , "def decide_action(oracle, variables, actions, step) do"
    , "  different_states = Enum.uniq_by(actions, fn(action) -> action[:state] end)"
    , ""
    , "  cond do"
    , "    Enum.count(different_states) == 1 ->"
    , "      Enum.at(actions, 0)[:state]"
    , "    true ->"
    , "      send oracle, {:choose, self(), actions}"
    , ""
    , "     receive do"
    , "       {:ok, n} -> Enum.at(actions, n)[:state]"
    , "       {:cancel} -> variables"
    , "       {:stop} -> exit(0)"
    , "     end"
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
    , "  next_variables = decide_action(oracle, variables, actions, step)"
    , "  send(oracle, {:notify, step, variables, next_variables})"
    , "  Process.sleep(2000)"
    , ""
    , "  main(oracle, next_variables, step + 1)"
    , "end"
    ]

waitLockFunction =
  unlines
    [ "def wait_lock(oracle) do"
    , "  send(oracle, {:lock, self()})"
    , "  receive do"
    , "    {:lock_acquired, state} -> IO.puts(\"Lock acquired\"); {map, _} = Map.split(state, shared_variables); map"
    , "    {:already_locked, _} -> IO.puts(\"Lock refused\"); Process.sleep(1000); wait_lock(oracle)"
    , "  end"
    , "end"
    ]

logState = "IO.puts (inspect variables)\n\n"

oracleDelaration = "require Oracle\n\n"
