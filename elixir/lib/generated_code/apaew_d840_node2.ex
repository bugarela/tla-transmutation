defmodule APAEWD840_node2 do
  require Oracle

  import APAEWD840

  def next(variables) do
    Enum.filter(
      List.flatten([
      %{ action: "PassToken(Lit (Num 2))", condition: pass_token_condition(variables, 2), state: pass_token(variables, 2) },
      Enum.map(MapSet.new([0, 1]), fn (i) -> [
        %{ action: "SendMsg(Lit (Num 2), #{inspect i})", condition: send_msg_condition(variables, 2, i), state: send_msg(variables, 2, i) }
      ] end
      ),
      %{ action: "Deactivate(Lit (Num 2))", condition: deactivate_condition(variables, 2), state: deactivate(variables, 2) }
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

