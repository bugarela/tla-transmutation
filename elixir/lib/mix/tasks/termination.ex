defmodule Mix.Tasks.Termination do
  @moduledoc "Runs blackblox testing using the oracle"
  @shortdoc "Runs trace checking for a witness"
  use Mix.Task

  @impl Mix.Task
  def run(_) do
    trace =  [
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}
    ]

    modules =  [
        EWD840_node0,
      EWD840_node1,
      EWD840_node2
    ]
    pids = Enum.map(modules, fn m -> spawn(m, :main, [self(), Enum.at(trace, 0), 0]) end)
    TraceCheckerOracle.start(trace, 0, nil, pids)
  end
end
