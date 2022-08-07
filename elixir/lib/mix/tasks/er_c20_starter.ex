defmodule Mix.Tasks.ErC20Starter do
  @moduledoc "Printed when the user requests `mix help echo`"
  @shortdoc "Echoes arguments"
  use Mix.Task
  import ERC20

  @impl Mix.Task
  def run(_) do
      variables = %{}
      initial_state = %{
  balance_of: Map.new(ERC20.addr, fn(a) -> {a, 100} end),
  allowance: Map.new((for x <- ERC20.addr, y <- ERC20.addr, do: {x, y}), fn(pair) -> {pair, 0} end),
  pending_transactions: MapSet.new([]),
  next_tx_id: 0,
  last_tx: %{ "id" => 0, "tag" => "None", "fail" => false }
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
