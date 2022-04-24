defmodule TraceRunner do
  @trace [
    %{ jarro_pequeno: 0, jarro_grande: 0 },
    %{ jarro_pequeno: 0, jarro_grande: 5 },
    %{ jarro_pequeno: 3, jarro_grande: 2 },
    %{ jarro_pequeno: 0, jarro_grande: 2 },
    %{ jarro_pequeno: 2, jarro_grande: 0 },
    %{ jarro_pequeno: 2, jarro_grande: 5 },
    %{ jarro_pequeno: 3, jarro_grande: 4 },
  ]

  def check(index, current_state, next_state) do
    IO.inspect(index)
    IO.inspect(current_state)
    IO.inspect(next_state)
    Enum.at(@trace, index) == current_state && Enum.at(@trace, index + 1) == next_state
  end

  def choose(index, actions) do
    IO.inspect(index)
    IO.inspect(actions)
    Enum.find_index(actions, fn a -> a[:state] == Enum.at(@trace, index+1) end)
  end
end
