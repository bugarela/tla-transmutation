module Snippets where

decideAction = unlines [
             "",
             "def decide_action(origin, actions) do",
             "  possible_actions = Enum.filter(actions, fn(action) -> action[:condition] end)",
             "  different_states = Enum.uniq_by(possible_actions, fn(action) -> action[:state] end)",
             "",
             "  if Enum.count(different_states) == 1 do",
             "    Enum.at(possible_actions, 0)[:state]",
             "  else",
             "    actions_names = Enum.map(possible_actions, fn(action) -> action[:action] end)",
             "    send @oracle, {self(), origin, actions_names}",
             "",
             "    n = receive do",
             "      {:ok, n} -> n",
             "    end",
             "",
             "    Enum.at(possible_actions, n)[:state]",
             "  end",
             "end"
             ]

logState = "IO.puts (inspect variables)\n\n"
