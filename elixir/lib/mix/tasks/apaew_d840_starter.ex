defmodule Mix.Tasks.ApaewD840Starter do
  @moduledoc "Printed when the user requests `mix help echo`"
  @shortdoc "Echoes arguments"
  use Mix.Task
  import APAEWD840

  @impl Mix.Task
  def run(_) do
      variables = %{}
      initial_state = %{
  active: Map.new(nodes(variables), fn(n) -> {n, true} end),
  color: Map.new(nodes(variables), fn(n) -> {n, "white"} end),
  tpos: 0,
  tcolor: "black"
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
