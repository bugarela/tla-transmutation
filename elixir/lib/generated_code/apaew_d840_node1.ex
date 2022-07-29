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

    next_variables = decide_action(oracle, variables, actions, step)
    send(oracle, {:notify, step, variables, next_variables})
    Process.sleep(2000)

    main(oracle, next_variables, step + 1)
  end
end

