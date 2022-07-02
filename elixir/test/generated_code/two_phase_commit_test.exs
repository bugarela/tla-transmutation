defmodule TwoPhaseCommitTest do
  use ExUnit.Case
  doctest TwoPhaseCommit
test "fromState 9" do
  variables = %{
  msgs: MapSet.new([]),
  rm_state: %{ r1: "working", r2: "working" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }]),
  rm_state: %{ r1: "working", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "working" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([]),
  rm_state: %{ r1: "aborted", r2: "working" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "working", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([]),
  rm_state: %{ r1: "working", r2: "aborted" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 10" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }]),
  rm_state: %{ r1: "working", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }]),
  rm_state: %{ r1: "aborted", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "working", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }]),
  rm_state: %{ r1: "working", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 11" do
  variables = %{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "working" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "working" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r1"])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 12" do
  variables = %{
  msgs: MapSet.new([]),
  rm_state: %{ r1: "aborted", r2: "working" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }]),
  rm_state: %{ r1: "aborted", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 13" do
  variables = %{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "working", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "working", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "working", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 14" do
  variables = %{
  msgs: MapSet.new([]),
  rm_state: %{ r1: "working", r2: "aborted" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }]),
  rm_state: %{ r1: "working", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 15" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "aborted", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 16" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }]),
  rm_state: %{ r1: "aborted", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }]),
  rm_state: %{ r1: "aborted", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 17" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "working", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "working", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 18" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }]),
  rm_state: %{ r1: "working", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }]),
  rm_state: %{ r1: "working", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 19" do
  variables = %{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "working" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r1"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "working" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r1"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r1"])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r1"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 20" do
  variables = %{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r1"])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 21" do
  variables = %{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r1"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 22" do
  variables = %{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 23" do
  variables = %{
  msgs: MapSet.new([]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "init",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 24" do
  variables = %{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "working", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "working", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r2"])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r2"])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r2"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "working", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 25" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "aborted", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "aborted", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 26" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 27" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 28" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 29" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 30" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "working", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "working", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 31" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "aborted", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 32" do
  variables = %{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r1"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r1"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r1", "r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 33" do
  variables = %{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r1"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r1"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 34" do
  variables = %{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r2"])
},
%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r1", "r2"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 35" do
  variables = %{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r2"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 36" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "working", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "working", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 37" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 38" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 39" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 40" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 41" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "aborted", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "aborted", r2: "working" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 42" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 43" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 44" do
  variables = %{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r1", "r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "init",
  tm_prepared: MapSet.new(["r1", "r2"])
},
%{
  msgs: MapSet.new([%{ type: "Commit" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 45" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 46" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 47" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "working", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "working", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 48" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new([])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 49" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 50" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 51" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 52" do
  variables = %{
  msgs: MapSet.new([%{ type: "Commit" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Commit" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "committed", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
},
%{
  msgs: MapSet.new([%{ type: "Commit" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "committed" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 53" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 54" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 55" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 56" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 57" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 58" do
  variables = %{
  msgs: MapSet.new([%{ type: "Commit" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "committed", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Commit" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "committed", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
},
%{
  msgs: MapSet.new([%{ type: "Commit" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "committed", r2: "committed" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 59" do
  variables = %{
  msgs: MapSet.new([%{ type: "Commit" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "committed" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Commit" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "committed" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
},
%{
  msgs: MapSet.new([%{ type: "Commit" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "committed", r2: "committed" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 60" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "prepared" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 61" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "prepared", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
},
%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 62" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 63" do
  variables = %{
  msgs: MapSet.new([%{ type: "Commit" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "committed", r2: "committed" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Commit" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "committed", r2: "committed" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

test "fromState 64" do
  variables = %{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}

  expectedStates = [%{
  msgs: MapSet.new([%{ type: "Abort" }, %{ type: "Prepared", rm: "r1" }, %{ type: "Prepared", rm: "r2" }]),
  rm_state: %{ r1: "aborted", r2: "aborted" },
  tm_state: "done",
  tm_prepared: MapSet.new(["r1", "r2"])
}]

  actions = TwoPhaseCommit.next(variables)
  states = Enum.map(actions, fn action -> action[:state] end)

  assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
  assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
  assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
end

end