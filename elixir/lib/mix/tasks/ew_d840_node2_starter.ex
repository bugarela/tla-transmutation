defmodule Mix.Tasks.EwD840Node2Starter do
  @moduledoc "Printed when the user requests `mix help echo`"
  @shortdoc "Echoes arguments"
  use Mix.Task
  import EWD840
  import EWD840_node2

  @impl Mix.Task
  def run(args) do
    variables = %{}
    initial_state = %{
  active: Map.new(nodes(variables), fn(n) -> {n, true} end),
  color: Map.new(nodes(variables), fn(n) -> {n, "white"} end),
  tpos: 0,
  tcolor: "black"
}
    oracle_host = String.to_atom(Enum.at(args, 0))
    Node.connect(oracle_host)
    oracle_pid = find_oracle()
    IO.puts(inspect(oracle_pid))
    main(oracle_pid, initial_state, 0)
  end

  def find_oracle() do
    o = :global.whereis_name("oracle")
    if o == :undefined do
      find_oracle()
    else
      o
    end
  end
end
