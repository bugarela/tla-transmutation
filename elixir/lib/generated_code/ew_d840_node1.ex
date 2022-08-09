defmodule EWD840_node1 do
  require Oracle

  import EWD840

  def next(variables) do
    Enum.filter(
      List.flatten([
      %{ action: "PassToken(Lit (Num 1))", condition: pass_token_condition(variables, 1), transition: fn (variables) -> pass_token(variables, 1) end },
      Enum.map(MapSet.new([0, 2]), fn (i) -> [
        %{ action: "SendMsg(Lit (Num 1), #{inspect i})", condition: send_msg_condition(variables, 1, i), transition: fn (variables) -> send_msg(variables, 1, i) end }
      ] end
      ),
      %{ action: "Deactivate(Lit (Num 1))", condition: deactivate_condition(variables, 1), transition: fn (variables) -> deactivate(variables, 1) end }
    ]),
      fn(action) -> action[:condition] end
    )
  end

  def main(oracle, private_variables, step) do
    shared_state = wait_lock(oracle)
    variables = Map.merge(private_variables, shared_state)

    actions = next(variables)

    next_variables = decide_action(oracle, variables, actions, step)
    send(oracle, {:notify, self(), variables, next_variables})
    Process.sleep(2000)

    main(oracle, next_variables, step + 1)
  end
end

