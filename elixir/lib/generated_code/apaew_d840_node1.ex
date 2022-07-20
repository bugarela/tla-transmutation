defmodule APAEWD840_node1 do
  require Oracle

  import APAEWD840
  @n "<value for N>"
  def n, do: @n



  def next(variables) do
    List.flatten([
      %{ action: "PassToken(Lit (Num 1))", condition: pass_token_condition(variables, 1), state: pass_token(variables, 1) },
      %{ action: "SendMsg(Lit (Num 1))", condition: send_msg_condition(variables, 1), state: send_msg(variables, 1) },
      %{ action: "Deactivate(Lit (Num 1))", condition: deactivate_condition(variables, 1), state: deactivate(variables, 1) }
    ])
  end

  def main(oracle, private_variables, step) do
    shared_state = wait_lock(oracle)
    variables = Map.merge(private_variables, shared_state)

    IO.puts(inspect(variables))
    actions = next(variables)

    next_variables = decide_action(oracle, actions, step)
    send(oracle, {:notify, step, variables, next_variables})

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
      {:ok, state} -> Map.split(state, shared_variables)
      {:already_locked, _} -> Process.sleep(1000); wait_lock(oracle)
    end
  end
end

