defmodule TraceCheckerOracle do
  def start(trace, step, lock, pids) do
    startWithValues(trace, step, lock, pids, [])
  end

  def startWithValues(trace, step, lock, pids, refused) do
    if step >= length(trace) - 1 do
      Enum.map(pids, fn pid -> send(pid, :stop) end)
      IO.puts("SUCCESS")
      exit(0)
    end

    if Enum.sort(Enum.uniq(pids)) == Enum.sort(Enum.uniq(refused)) do
      IO.puts("FAILURE")
      exit(1)
    end

    current_variables = Enum.at(trace, step)

    ref = Process.monitor(if lock != nil, do: lock, else: self())

    receive do
      {:lock, p} ->
        IO.inspect(lock)

        if lock != nil do
          send(p, {:already_locked, %{}})
        else
          send(p, {:lock_acquired, current_variables})
          startWithValues(trace, step, p, pids, refused)
        end

      {:notify, p, current_state, next_state} ->
        if current_state != next_state do
          result = TraceRunner.check(trace, step, current_state, next_state)
          IO.puts("Step: #{step + 1}")
          IO.inspect(result)
          IO.inspect(next_state)
          startWithValues(trace, step + 1, nil, pids, [])
        else
          startWithValues(trace, step, nil, pids, [p | refused])
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
        Process.sleep(2000)
        exit(1)
    end

    startWithValues(trace, step, lock, pids, refused)
  end
end
