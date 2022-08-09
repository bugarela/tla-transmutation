defmodule Mix.Tasks.TrafficSemaphoresMainStarter do
  @moduledoc "Printed when the user requests `mix help echo`"
  @shortdoc "Echoes arguments"
  use Mix.Task
  import TrafficSemaphores
  import TrafficSemaphores_main

  @impl Mix.Task
  def run(args) do
    variables = %{}
    initial_state = %{
  colors: Map.new(TrafficSemaphores.semaphores, fn(s) -> {s, "red"} end),
  next_to_open: 0
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
