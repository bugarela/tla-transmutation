defmodule Mix.Tasks.LevelEqualsFour do
  @moduledoc "Runs blackblox testing using the oracle"
  @shortdoc "Runs trace checking for a witness"
  use Mix.Task

  @impl Mix.Task
  def run(_) do
    trace =  [
%{
  jarro_pequeno: 0,
  jarro_grande: 0
},
%{
  jarro_pequeno: 0,
  jarro_grande: 5
},
%{
  jarro_pequeno: 3,
  jarro_grande: 2
},
%{
  jarro_pequeno: 0,
  jarro_grande: 2
},
%{
  jarro_pequeno: 2,
  jarro_grande: 0
},
%{
  jarro_pequeno: 2,
  jarro_grande: 5
},
%{
  jarro_pequeno: 3,
  jarro_grande: 4
}
    ]

    oracle = spawn(TraceCheckerOracle, :start, [trace])
    JarrosDeAgua.main(oracle, Enum.at(trace, 0), 0)
  end
end
