defmodule RandomOracle do
  def start(current_variables, step, lock) do
    IO.puts("RandomOracle at [#{inspect(self())}] is listening")
    ref = Process.monitor(if lock != nil, do: lock, else: self())

    receive do
      {:choose, p, _, as} -> send(p, {:ok, random_choice(as)})
      {:lock, p} -> if lock, do: send(p, {:already_locked, %{}}), else: lock = p; send(p, {:ok, current_variables})
      # Receive state and update shared variables
      {:DOWN, ^ref, _, _, _} -> IO.puts "Process #{inspect(ref)} is down"; lock = nil
    end

    variables = current_variables

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
