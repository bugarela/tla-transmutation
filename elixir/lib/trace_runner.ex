defmodule TraceRunner do
  def check(trace, index, current_state, next_state) do
    Enum.at(trace, index) == current_state && Enum.at(trace, index + 1) == next_state
  end

  def choose(trace, index, states) do
    # IO.inspect(states)
    # IO.inspect(Enum.map(actions, fn a -> a[:state][:pending_transactions] end), limit: 100)
    r = Enum.find_index(states, fn s -> s == Enum.at(trace, index + 1) end)

    if !r do
      IO.puts("Towards state: #{index + 1}")
      IO.inspect(Enum.at(trace, index + 1))
      # IO.inspect(Enum.map(states, fn a -> a[:pending_transactions] end), limit: 1000)
    end

    # if !r do
    #   IO.inspect(states)
    #   {i, _} = Integer.parse(IO.gets("Next Action: "))
    # end

    r
  end
end
