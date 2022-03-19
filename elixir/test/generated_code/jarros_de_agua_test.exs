defmodule JarrosDeAguaTest do
  use ExUnit.Case
  doctest JarrosDeAgua

  test "iterates" do
    variables = %{
      jarro_grande: 0,
      jarro_pequeno: 0
    }

    actions = JarrosDeAgua.next(variables)
    states = Enum.map(actions, fn action -> action[:state] end)

    expectedStates = [
      %{jarro_grande: 0, jarro_pequeno: 3},
      %{jarro_grande: 5, jarro_pequeno: 0},
      %{jarro_grande: 0, jarro_pequeno: 0},
      # %{jarro_grande: 0, jarro_pequeno: 0},
      # %{jarro_grande: 0, jarro_pequeno: 0},
      # %{jarro_grande: 0, jarro_pequeno: 0},
    ]

    assert Enum.count(Enum.dedup(states)) == Enum.count(Enum.dedup(expectedStates))
    assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  end
end
