defmodule TrafficSemaphores do
  def shared_variables do
    [
      :colors,
      :next_to_open,
    ]
  end
  require Oracle
  @semaphores MapSet.new([0, 1])
  def semaphores, do: @semaphores


  def turn_green_condition(variables, s) do
    Enum.all?([Enum.all?(@semaphores, fn(s2) -> variables[:colors][s2] == "red" end), variables[:next_to_open] == s])
  end

  def turn_green(variables, s) do
    %{
      colors: variables[:colors]|>Map.put(s, "green"),
      next_to_open: rem((s + 1), (Enum.count(@semaphores)))
    }
  end


  def turn_yellow_condition(variables, s) do
    variables[:colors][s] == "green"
  end

  def turn_yellow(variables, s) do
    %{
      colors: variables[:colors]|>Map.put(s, "yellow"),
      next_to_open: variables[:next_to_open]
    }
  end


  def turn_red_condition(variables, s) do
    variables[:colors][s] == "yellow"
  end

  def turn_red(variables, s) do
    %{
      colors: variables[:colors]|>Map.put(s, "red"),
      next_to_open: variables[:next_to_open]
    }
  end


  # "Spec": OperEx "AND" [OperEx "OPER_APP" [NameEx "Init"],OperEx "GLOBALLY" [OperEx "STUTTER" [OperEx "OPER_APP" [NameEx "Next"],OperEx "TUPLE" [NameEx "colors",NameEx "next_to_open"]]]]

  def decide_action(oracle, variables, actions, step) do
    different_states = Enum.uniq(Enum.map(actions, fn(action) -> action[:transition].(variables) end))

    cond do
      Enum.count(different_states) == 1 ->
        Enum.at(different_states, 0)
      true ->
        send oracle, {:choose, self(), different_states}

       receive do
         {:ok, n} -> Enum.at(different_states, n)
         {:cancel} -> variables
         {:stop} -> exit(0)
       end
    end
  end

  def wait_lock(oracle) do
    send(oracle, {:lock, self()})
    receive do
      {:lock_acquired, state} -> IO.puts("Lock acquired"); {map, _} = Map.split(state, shared_variables); map
      {:already_locked, _} -> IO.puts("Lock refused"); Process.sleep(1000); wait_lock(oracle)
    end
  end
end

