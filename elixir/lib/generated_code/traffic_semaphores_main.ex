defmodule TrafficSemaphores_main do
  require Oracle

  import TrafficSemaphores

  def next(variables) do
    Enum.filter(
      List.flatten([
      Enum.map(MapSet.new([0, 1]), fn (s) -> [
        %{ action: "TurnGreen(#{inspect s})", condition: turn_green_condition(variables, s), state: turn_green(variables, s) },
        %{ action: "TurnYellow(#{inspect s})", condition: turn_yellow_condition(variables, s), state: turn_yellow(variables, s) },
        %{ action: "TurnRed(#{inspect s})", condition: turn_red_condition(variables, s), state: turn_red(variables, s) }
      ] end
      )
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

