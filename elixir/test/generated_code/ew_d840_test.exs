defmodule EWD840Test do
  use ExUnit.Case
  doctest EWD840
test "fromState 12" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
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
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 13" do
  variables = %{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 14" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 15" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 16" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 17" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 18" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 19" do
  variables = %{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 20" do
  variables = %{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
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
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 21" do
  variables = %{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 22" do
  variables = %{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 23" do
  variables = %{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 24" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 25" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 26" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 27" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 28" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 29" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 30" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 31" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 32" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 33" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 34" do
  variables = %{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 35" do
  variables = %{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 36" do
  variables = %{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 37" do
  variables = %{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 38" do
  variables = %{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 39" do
  variables = %{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 40" do
  variables = %{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 41" do
  variables = %{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 42" do
  variables = %{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 43" do
  variables = %{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 44" do
  variables = %{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 45" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 46" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 47" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 48" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 49" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 50" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 51" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 52" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 53" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 54" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 55" do
  variables = %{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 56" do
  variables = %{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 57" do
  variables = %{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 58" do
  variables = %{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 59" do
  variables = %{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 60" do
  variables = %{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 61" do
  variables = %{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 62" do
  variables = %{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 63" do
  variables = %{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 64" do
  variables = %{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 65" do
  variables = %{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
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
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 66" do
  variables = %{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 67" do
  variables = %{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 68" do
  variables = %{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 69" do
  variables = %{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 70" do
  variables = %{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 71" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 72" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 73" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 74" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 75" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 76" do
  variables = %{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 77" do
  variables = %{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 78" do
  variables = %{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 79" do
  variables = %{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 80" do
  variables = %{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 81" do
  variables = %{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 82" do
  variables = %{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 83" do
  variables = %{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 84" do
  variables = %{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 85" do
  variables = %{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 86" do
  variables = %{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 87" do
  variables = %{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 88" do
  variables = %{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 89" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 90" do
  variables = %{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 91" do
  variables = %{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 92" do
  variables = %{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 93" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 94" do
  variables = %{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 95" do
  variables = %{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 96" do
  variables = %{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 97" do
  variables = %{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 98" do
  variables = %{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 99" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 100" do
  variables = %{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 101" do
  variables = %{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 102" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}

  expectedStates = []

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 103" do
  variables = %{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 104" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 105" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 106" do
  variables = %{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 107" do
  variables = %{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 108" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 109" do
  variables = %{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "black",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 1,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 110" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 111" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 112" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 113" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 114" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "white", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 115" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 116" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 117" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 118" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 119" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => true, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 120" do
  variables = %{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => true, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => false, 2 => true },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => true, 1 => true, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
},
%{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

test "fromState 121" do
  variables = %{
  tpos: 0,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "black", 1 => "black", 2 => "white" }
}

  expectedStates = [%{
  tpos: 2,
  active: %{ 0 => false, 1 => false, 2 => false },
  tcolor: "white",
  color: %{ 0 => "white", 1 => "black", 2 => "white" }
}]

  actions = List.flatten([EWD840_node0.next(variables), EWD840_node1.next(variables), EWD840_node2.next(variables)])
  states = Enum.map(actions, fn action -> action[:transition].(variables) end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
end

end