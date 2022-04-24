 defmodule TestOracle do
  def start do
    :global.register_name("oracle", self())

    listen()
  end

  def listen() do
    IO.puts("TestOracle at [#{inspect(self())}] is listening")

    receive do
      {:notify, step, current_state, next_state} -> IO.puts(TraceRunner.check(step, current_state, next_state))
      {:choose, p, step, as} ->
        choice = TraceRunner.choose(step, as)
        if choice != nil do
          send(p, {:ok, choice})
        else
          send(p, {:stop})
        end
    end

    listen()
  end
end
