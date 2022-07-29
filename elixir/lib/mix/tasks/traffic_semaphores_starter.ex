defmodule Mix.Tasks.TrafficSemaphoresStarter do
  @moduledoc "Printed when the user requests `mix help echo`"
  @shortdoc "Echoes arguments"
  use Mix.Task
  import TrafficSemaphores

  @impl Mix.Task
  def run(_) do
      variables = %{}
      initial_state = %{
  colors: Map.new(TrafficSemaphores.semaphores, fn(s) -> {s, "red"} end),
  next_to_open: 0
}

    oracle = spawn(RandomOracle, :start, [initial_state, 0, nil])
    :global.register_name("oracle", oracle)

    ref = Process.monitor(oracle)

     receive do
       {:DOWN, ^ref, _, _, _} ->
         IO.puts("Oracle is down")
    end
  end
end
