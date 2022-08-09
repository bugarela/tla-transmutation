defmodule Mix.Tasks.SingleSemaphoreLoop do
  @moduledoc "Runs blackblox testing using the oracle"
  @shortdoc "Runs trace checking for a witness"
  use Mix.Task

  @impl Mix.Task
  def run(_) do
    trace =  [
%{
  colors: %{ 0 => "red", 1 => "red" },
  next_to_open: 0
},
%{
  colors: %{ 0 => "red", 1 => "green" },
  next_to_open: 0
},
%{
  colors: %{ 0 => "red", 1 => "yellow" },
  next_to_open: 0
},
%{
  colors: %{ 0 => "red", 1 => "red" },
  next_to_open: 0
}
    ]

    modules =  [
        TrafficSemaphores_main
    ]
    pids = Enum.map(modules, fn m -> spawn(m, :main, [self(), Enum.at(trace, 0), 0]) end)
    TraceCheckerOracle.start(trace, 0, nil, pids)
  end
end
