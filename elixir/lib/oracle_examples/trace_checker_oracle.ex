 defmodule TraceCheckerOracle do
  def start(trace) do
    :global.register_name("oracle", self())

    listen(trace)
  end

  def listen(trace) do
    IO.puts("TestOracle at [#{inspect(self())}] is listening")

    receive do
      {:notify, step, current_state, next_state} -> IO.puts(TraceRunner.check(trace, step, current_state, next_state))
      {:choose, p, step, as} ->
        choice = TraceRunner.choose(trace, step, as)
        if choice != nil do
          send(p, {:ok, choice})
        else
          send(p, {:stop})
        end
    end

    listen(trace)
  end
end
