defmodule Mix.Tasks.Startmodel do
  @moduledoc "Printed when the user requests `mix help echo`"
  @shortdoc "Echoes arguments"
  use Mix.Task

  @impl Mix.Task
  def run(_) do
    oracle = spawn(TestOracle, :start, [])
    JarrosDeAgua.main(oracle, %{jarro_grande: 0, jarro_pequeno: 0}, 0)
  end
end
