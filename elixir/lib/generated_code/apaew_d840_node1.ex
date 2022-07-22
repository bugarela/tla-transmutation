defmodule APAEWD840_node1 do
  require Oracle

  import APAEWD840

  def next(variables) do
    Enum.filter(
      List.flatten([
      %{ action: "PassToken(Lit (Num 1))", condition: pass_token_condition(variables, 1), state: pass_token(variables, 1) },
      Enum.map(MapSet.new([0, 2]), fn (i) -> [
        %{ action: "SendMsg(Lit (Num 1), #{inspect i})", condition: send_msg_condition(variables, 1, i), state: send_msg(variables, 1, i) }
      ] end
      ),
      %{ action: "Deactivate(Lit (Num 1))", condition: deactivate_condition(variables, 1), state: deactivate(variables, 1) }
    ]),
      fn(action) -> action[:condition] end
    )
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
    different_states = Enum.uniq_by(actions, fn(action) -> action[:state] end)

    cond do
      Enum.count(different_states) == 1 ->
        Enum.at(actions, 0)[:state]
      Enum.empty?(different_states) ->
        IO.puts("DEADLOCK")
        exit(0)
      true ->
        send oracle, {:choose, self(), actions}

        n = receive do
          {:ok, n} -> n
          {:stop} -> exit(0)
        end

        Enum.at(actions, n)[:state]
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

