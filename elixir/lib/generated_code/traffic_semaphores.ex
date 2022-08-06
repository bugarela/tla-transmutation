defmodule TrafficSemaphores do
  def shared_variables do
    [
      :colors,
      :next_to_open,
    ]
  end
  require Oracle
  @semaphores "<value for SEMAPHORES>"
  def semaphores, do: @semaphores


  def turn_green_condition(variables, s) do
    Enum.all?(@semaphores, fn(s2) -> variables[:colors][s2] == "red" end)
  end

  def turn_green(variables, s) do
    %{
      colors: Map.put(variables[:colors], s, "green"),
      next_to_open: variables[:next_to_open]
    }
  end


  def turn_yellow_condition(variables, s) do
    variables[:colors][s] == "green"
  end

  def turn_yellow(variables, s) do
    %{
      colors: Map.put(variables[:colors], s, "yellow"),
      next_to_open: variables[:next_to_open]
    }
  end


  def turn_red_condition(variables, s) do
    variables[:colors][s] == "yellow"
  end

  def turn_red(variables, s) do
    %{
      colors: Map.put(variables[:colors], s, "red"),
      next_to_open: variables[:next_to_open]
    }
  end



  def decide_action(oracle, variables, actions, step) do
    different_states = Enum.uniq_by(actions, fn(action) -> action[:state] end)

    cond do
      Enum.count(different_states) == 1 ->
        Enum.at(actions, 0)[:state]
      true ->
        send oracle, {:choose, self(), actions}

       receive do
         {:ok, n} -> Enum.at(actions, n)[:state]
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

