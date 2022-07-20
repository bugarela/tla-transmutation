defmodule RandomOracle do
  def start(current_variables, step, lock) do
    ref = Process.monitor(if lock != nil, do: lock, else: self())
    IO.puts("RandomOracle at #{inspect(self())} is listening")

    receive do
      {:lock, p} -> IO.inspect(lock); if lock, do: send(p, {:already_locked, %{}}), else: send(p, {:ok, current_variables}); start(current_variables, step, p)
      {:choose, p, _, as} -> send(p, {:ok, random_choice(as)})
      # Receive state and update shared variables
      {:DOWN, ^ref, _, _, _} -> IO.puts "Process #{inspect(ref)} is down"; start(current_variables, step, nil)
    end

    variables = current_variables
    IO.inspect(variables)

    start(variables, (if variables != current_variables, do: step + 1, else: step), lock)
  end

  def random_choice(as) do
    Process.sleep(1000)
    n = length(as) - 1
    choice = Enum.random(0..n)
    IO.puts("From #{inspect(as)}, oracle chose #{inspect(Enum.at(as, choice))}\n")

    choice
  end
end
