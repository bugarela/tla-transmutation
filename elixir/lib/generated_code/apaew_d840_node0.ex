defmodule APAEWD840_node0 do
  require Oracle

  import APAEWD840

  def next(variables) do
    List.flatten([
      %{ action: "InitiateProbe()", condition: initiate_probe_condition(variables), state: initiate_probe(variables) },
      Enum.map(MapSet.new([1, 2]), fn (i) -> [
        %{ action: "SendMsg(Lit (Num 0), #{inspect i})", condition: send_msg_condition(variables, 0, i), state: send_msg(variables, 0, i) }
      ] end
      ),
      %{ action: "Deactivate(Lit (Num 0))", condition: deactivate_condition(variables, 0), state: deactivate(variables, 0) }
    ])
  end

  def main(oracle, private_variables, step) do
    shared_state = wait_lock(oracle)
    variables = Map.merge(private_variables, shared_state)

    IO.puts(inspect(variables))
    actions = next(variables)

    next_variables = decide_action(oracle, actions, step)
    send(oracle, {:notify, step, variables, next_variables})
    Process.sleep(2000)

    main(oracle, next_variables, step + 1)
  end

  def decide_action(oracle, actions, step) do
    possible_actions = Enum.filter(actions, fn(action) -> action[:condition] end)
    different_states = Enum.uniq_by(possible_actions, fn(action) -> action[:state] end)

    cond do
      Enum.count(different_states) == 1 ->
        Enum.at(possible_actions, 0)[:state]
      Enum.empty?(different_states) ->
        IO.puts("DEADLOCK")
        exit(0)
      true ->
        send oracle, {:choose, self(), possible_actions}

        n = receive do
          {:ok, n} -> n
          {:stop} -> exit(0)
        end

        Enum.at(possible_actions, n)[:state]
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

