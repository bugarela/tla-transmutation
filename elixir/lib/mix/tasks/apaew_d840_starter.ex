defmodule Mix.Tasks.ApaewD840Starter do
  @moduledoc "Printed when the user requests `mix help echo`"
  @shortdoc "Echoes arguments"
  use Mix.Task
  import APAEWD840

  @impl Mix.Task
  def run(_) do
      variables = %{}
      initial_state = %{
  active: MapSet.new(nodes(variables), fn(n) -> true end),
  color: MapSet.new(nodes(variables), fn(n) -> "white" end),
  tpos: 0,
  tcolor: "black"
}

    oracle = spawn(RandomOracle, :start, [initial_state, 0, nil])
    a = :global.register_name("oracle", oracle)
    IO.puts(inspect(a))
    aoracle = :global.whereis_name("oracle")
    IO.puts(inspect(aoracle))

    ref = Process.monitor(oracle)

     receive do
       {:DOWN, ^ref, _, _, _} ->
         IO.puts("Oracle is down")
    end
  end
end
