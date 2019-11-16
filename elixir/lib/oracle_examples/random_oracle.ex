defmodule RandomOracle do
  def start do
    IO.puts "RandomOracle at [#{inspect self}] is listening"

    receive do
      {p, as} -> send p, {:ok, random_choice(as)}
    end
    start()
  end

  def random_choice(as) do
    Process.sleep(1000)
    n = length(as) - 1
    choice = Enum.random(0..n)
    IO.puts "From #{inspect as}, oracle chose #{Enum.at(as, choice)}\n"

    choice
  end
end
