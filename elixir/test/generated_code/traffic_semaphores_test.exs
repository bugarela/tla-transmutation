defmodule TrafficSemaphoresTest do
  use ExUnit.Case
  doctest TrafficSemaphores
test "fromState 7" do
  variables = %{
  colors: %{ 0 => "red", 1 => "red" },
  next_to_open: 0
}

  expectedStates = [%{
  colors: %{ 0 => "green", 1 => "red" },
  next_to_open: 1
}]

  actions = List.flatten([TrafficSemaphores_main.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 8" do
  variables = %{
  colors: %{ 0 => "green", 1 => "red" },
  next_to_open: 1
}

  expectedStates = [%{
  colors: %{ 0 => "yellow", 1 => "red" },
  next_to_open: 1
}]

  actions = List.flatten([TrafficSemaphores_main.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 9" do
  variables = %{
  colors: %{ 0 => "yellow", 1 => "red" },
  next_to_open: 1
}

  expectedStates = [%{
  colors: %{ 0 => "red", 1 => "red" },
  next_to_open: 1
}]

  actions = List.flatten([TrafficSemaphores_main.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 10" do
  variables = %{
  colors: %{ 0 => "red", 1 => "red" },
  next_to_open: 1
}

  expectedStates = [%{
  colors: %{ 0 => "red", 1 => "green" },
  next_to_open: 0
}]

  actions = List.flatten([TrafficSemaphores_main.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 11" do
  variables = %{
  colors: %{ 0 => "red", 1 => "green" },
  next_to_open: 0
}

  expectedStates = [%{
  colors: %{ 0 => "red", 1 => "yellow" },
  next_to_open: 0
}]

  actions = List.flatten([TrafficSemaphores_main.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 12" do
  variables = %{
  colors: %{ 0 => "red", 1 => "yellow" },
  next_to_open: 0
}

  expectedStates = [%{
  colors: %{ 0 => "red", 1 => "red" },
  next_to_open: 0
}]

  actions = List.flatten([TrafficSemaphores_main.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

end