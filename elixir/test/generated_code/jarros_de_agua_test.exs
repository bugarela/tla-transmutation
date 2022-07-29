# defmodule JarrosDeAguaTest do
#   use ExUnit.Case
#   doctest JarrosDeAgua
# test "fromState 9" do
#   variables = %{
#   jarro_pequeno: 0,
#   jarro_grande: 0
# }

#   expectedStates = [%{
#   jarro_pequeno: 0,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 5
# }]

#   actions = JarrosDeAgua.next(variables)
#   states = Enum.map(actions, fn action -> action[:state] end)

#   assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
#   assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
#   assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
# end

# test "fromState 10" do
#   variables = %{
#   jarro_pequeno: 3,
#   jarro_grande: 0
# }

#   expectedStates = [%{
#   jarro_pequeno: 0,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 3
# }]

#   actions = JarrosDeAgua.next(variables)
#   states = Enum.map(actions, fn action -> action[:state] end)

#   assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
#   assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
#   assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
# end

# test "fromState 11" do
#   variables = %{
#   jarro_pequeno: 0,
#   jarro_grande: 5
# }

#   expectedStates = [%{
#   jarro_pequeno: 0,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 2
# }]

#   actions = JarrosDeAgua.next(variables)
#   states = Enum.map(actions, fn action -> action[:state] end)

#   assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
#   assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
#   assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
# end

# test "fromState 12" do
#   variables = %{
#   jarro_pequeno: 3,
#   jarro_grande: 5
# }

#   expectedStates = [%{
#   jarro_pequeno: 3,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 5
# }]

#   actions = JarrosDeAgua.next(variables)
#   states = Enum.map(actions, fn action -> action[:state] end)

#   assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
#   assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
#   assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
# end

# test "fromState 13" do
#   variables = %{
#   jarro_pequeno: 0,
#   jarro_grande: 3
# }

#   expectedStates = [%{
#   jarro_pequeno: 0,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 3
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 3
# }]

#   actions = JarrosDeAgua.next(variables)
#   states = Enum.map(actions, fn action -> action[:state] end)

#   assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
#   assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
#   assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
# end

# test "fromState 14" do
#   variables = %{
#   jarro_pequeno: 3,
#   jarro_grande: 2
# }

#   expectedStates = [%{
#   jarro_pequeno: 3,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 2
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 2
# }]

#   actions = JarrosDeAgua.next(variables)
#   states = Enum.map(actions, fn action -> action[:state] end)

#   assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
#   assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
#   assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
# end

# test "fromState 15" do
#   variables = %{
#   jarro_pequeno: 3,
#   jarro_grande: 3
# }

#   expectedStates = [%{
#   jarro_pequeno: 3,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 3
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 3
# },
# %{
#   jarro_pequeno: 1,
#   jarro_grande: 5
# }]

#   actions = JarrosDeAgua.next(variables)
#   states = Enum.map(actions, fn action -> action[:state] end)

#   assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
#   assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
#   assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
# end

# test "fromState 16" do
#   variables = %{
#   jarro_pequeno: 0,
#   jarro_grande: 2
# }

#   expectedStates = [%{
#   jarro_pequeno: 0,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 2
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 2
# },
# %{
#   jarro_pequeno: 2,
#   jarro_grande: 0
# }]

#   actions = JarrosDeAgua.next(variables)
#   states = Enum.map(actions, fn action -> action[:state] end)

#   assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
#   assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
#   assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
# end

# test "fromState 17" do
#   variables = %{
#   jarro_pequeno: 1,
#   jarro_grande: 5
# }

#   expectedStates = [%{
#   jarro_pequeno: 0,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 3
# },
# %{
#   jarro_pequeno: 1,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 1,
#   jarro_grande: 0
# }]

#   actions = JarrosDeAgua.next(variables)
#   states = Enum.map(actions, fn action -> action[:state] end)

#   assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
#   assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
#   assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
# end

# test "fromState 18" do
#   variables = %{
#   jarro_pequeno: 2,
#   jarro_grande: 0
# }

#   expectedStates = [%{
#   jarro_pequeno: 0,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 2
# },
# %{
#   jarro_pequeno: 2,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 2,
#   jarro_grande: 5
# }]

#   actions = JarrosDeAgua.next(variables)
#   states = Enum.map(actions, fn action -> action[:state] end)

#   assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
#   assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
#   assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
# end

# test "fromState 19" do
#   variables = %{
#   jarro_pequeno: 1,
#   jarro_grande: 0
# }

#   expectedStates = [%{
#   jarro_pequeno: 0,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 1,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 1,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 1
# }]

#   actions = JarrosDeAgua.next(variables)
#   states = Enum.map(actions, fn action -> action[:state] end)

#   assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
#   assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
#   assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
# end

# test "fromState 20" do
#   variables = %{
#   jarro_pequeno: 2,
#   jarro_grande: 5
# }

#   expectedStates = [%{
#   jarro_pequeno: 0,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 2,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 2,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 4
# }]

#   actions = JarrosDeAgua.next(variables)
#   states = Enum.map(actions, fn action -> action[:state] end)

#   assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
#   assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
#   assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
# end

# test "fromState 21" do
#   variables = %{
#   jarro_pequeno: 0,
#   jarro_grande: 1
# }

#   expectedStates = [%{
#   jarro_pequeno: 0,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 1,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 1
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 1
# }]

#   actions = JarrosDeAgua.next(variables)
#   states = Enum.map(actions, fn action -> action[:state] end)

#   assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
#   assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
#   assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
# end

# test "fromState 22" do
#   variables = %{
#   jarro_pequeno: 3,
#   jarro_grande: 4
# }

#   expectedStates = [%{
#   jarro_pequeno: 3,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 2,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 4
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 4
# }]

#   actions = JarrosDeAgua.next(variables)
#   states = Enum.map(actions, fn action -> action[:state] end)

#   assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
#   assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
#   assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
# end

# test "fromState 23" do
#   variables = %{
#   jarro_pequeno: 3,
#   jarro_grande: 1
# }

#   expectedStates = [%{
#   jarro_pequeno: 3,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 1
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 1
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 4
# }]

#   actions = JarrosDeAgua.next(variables)
#   states = Enum.map(actions, fn action -> action[:state] end)

#   assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
#   assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
#   assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
# end

# test "fromState 24" do
#   variables = %{
#   jarro_pequeno: 0,
#   jarro_grande: 4
# }

#   expectedStates = [%{
#   jarro_pequeno: 0,
#   jarro_grande: 0
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 5
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 4
# },
# %{
#   jarro_pequeno: 3,
#   jarro_grande: 1
# },
# %{
#   jarro_pequeno: 0,
#   jarro_grande: 4
# }]

#   actions = JarrosDeAgua.next(variables)
#   states = Enum.map(actions, fn action -> action[:state] end)

#   assert Enum.sort(Enum.uniq(states)) == Enum.sort(Enum.uniq(expectedStates))
#   assert Enum.all?(actions, fn action -> Enum.member?(expectedStates, action[:state]) end)
#   assert Enum.all?(expectedStates, fn s -> Enum.member?(states, s) end)
# end

# end
