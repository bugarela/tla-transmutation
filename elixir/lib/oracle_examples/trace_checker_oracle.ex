defmodule TraceCheckerOracle do
  def start(trace, step, lock, pids) do
    if step >= length(trace) - 1 do
      Enum.map(pids, fn pid -> send(pid, :stop) end)
      IO.puts("SUCCESS")
      exit(0)
    end

    current_variables = Enum.at(trace, step)

    ref = Process.monitor(if lock != nil, do: lock, else: self())
    IO.puts("TraceCheckerOracle at #{inspect(self())} is listening")

    receive do
      {:lock, p} ->
        IO.inspect(lock)

        if lock != nil do
          send(p, {:already_locked, %{}})
        else
          send(p, {:lock_acquired, current_variables})
          start(trace, step, p, pids)
        end

      {:notify, _, current_state, next_state} ->
        if current_state != next_state do
          result = TraceRunner.check(trace, step, current_state, next_state)
          IO.puts("Step: #{step + 1}")
          IO.inspect(result)
          IO.inspect(next_state)
          start(trace, step + 1, nil, pids)
        else
          start(trace, step, nil, pids)
        end

      {:choose, p, as} ->
        choice = TraceRunner.choose(trace, step, as)

        if choice != nil do
          send(p, {:ok, choice})
        else
          send(p, {:cancel})
        end

      {:DOWN, ^ref, _, _, _} ->
        IO.puts("Process #{inspect(ref)} is down")
        start(trace, step, nil, pids)
    end

    start(trace, step, lock, pids)
  end
end
