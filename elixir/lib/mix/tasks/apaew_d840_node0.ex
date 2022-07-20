defmodule Mix.Tasks.ApaewD840Node0 do
  @moduledoc "Printed when the user requests `mix help echo`"
  @shortdoc "Echoes arguments"
  use Mix.Task
  import APAEWD840
  import APAEWD840_node0

  @impl Mix.Task
  def run(args) do
     variables = %{}
      initial_state = %{
  active: MapSet.new(nodes(variables), fn(n) -> true end),
  color: MapSet.new(nodes(variables), fn(n) -> "white" end),
  tpos: 0,
  tcolor: "black"
}

    oracle_host = String.to_atom(Enum.at(args, 0))
    IO.inspect(oracle_host)
    result = Node.connect(oracle_host)
    IO.inspect(result)
    IO.inspect(Node.ping(oracle_host))
    oracle = :global.whereis_name("oracle")
    IO.puts(inspect(oracle))
    main(oracle, initial_state, 0)

  end
end
