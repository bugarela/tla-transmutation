defmodule RandomOracle do
  def start(current_variables, step, lock) do
    ref = Process.monitor(if lock != nil, do: lock, else: self())
    IO.puts("RandomOracle at #{inspect(self())} is listening")

    receive do
      {:lock, p} -> IO.inspect(lock); if lock != nil, do: send(p, {:already_locked, %{}}), else: send(p, {:lock_acquired, current_variables}); start(current_variables, step, p)
      {:choose, p, as} -> send(p, {:ok, random_choice(as)}); start(current_variables, step, lock)
      {:notify, _, _, variables} -> IO.puts("notified"); IO.inspect(variables); start(variables, step + 1, nil)
      {:DOWN, ^ref, _, _, _} -> IO.puts "Process #{inspect(ref)} is down"; start(current_variables, step, nil)
    end
  end

  def random_choice(as) do
    Process.sleep(500)
    n = length(as) - 1
    choice = Enum.random(0..n)
    IO.puts("From #{inspect(as)}, oracle chose #{inspect(Enum.at(as, choice))}\n")

    choice
  end
end
