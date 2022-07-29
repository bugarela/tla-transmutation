defmodule APAEWD840_node0 do
  require Oracle

  import APAEWD840

  def next(variables) do
    Enum.filter(
      List.flatten([
      %{ action: "InitiateProbe()", condition: initiate_probe_condition(variables), state: initiate_probe(variables) },
      Enum.map(MapSet.new([1, 2]), fn (i) -> [
        %{ action: "SendMsg(Lit (Num 0), #{inspect i})", condition: send_msg_condition(variables, 0, i), state: send_msg(variables, 0, i) }
      ] end
      ),
      %{ action: "Deactivate(Lit (Num 0))", condition: deactivate_condition(variables, 0), state: deactivate(variables, 0) }
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

