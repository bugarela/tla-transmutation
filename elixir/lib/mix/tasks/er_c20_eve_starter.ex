defmodule Mix.Tasks.ErC20EveStarter do
  @moduledoc "Printed when the user requests `mix help echo`"
  @shortdoc "Echoes arguments"
  use Mix.Task
  import ERC20
  import ERC20_eve

  @impl Mix.Task
  def run(args) do
    variables = %{}
    initial_state = %{
  balance_of: Map.new(ERC20.addr, fn(a) -> {a, 100} end),
  allowance: Map.new((for x <- ERC20.addr, y <- ERC20.addr, do: {x, y}), fn(pair) -> {pair, 0} end),
  pending_transactions: MapSet.new([]),
  next_tx_id: 0,
  last_tx: %{ "id" => 0, "tag" => "None", "fail" => false }
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
