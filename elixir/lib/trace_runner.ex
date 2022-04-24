defmodule TraceRunner do

  def check(trace, index, current_state, next_state) do
    IO.inspect(index)
    IO.inspect(current_state)
    IO.inspect(next_state)
    Enum.at(trace, index) == current_state && Enum.at(trace, index + 1) == next_state
  end

  def choose(trace, index, actions) do
    IO.inspect(index)
    IO.inspect(actions)
    Enum.find_index(actions, fn a -> a[:state] == Enum.at(trace, index+1) end)
  end
end
