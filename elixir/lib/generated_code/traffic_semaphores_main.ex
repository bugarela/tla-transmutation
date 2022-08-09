defmodule TrafficSemaphores_main do
  require Oracle

  import TrafficSemaphores

  def next(variables) do
    Enum.filter(
      List.flatten([
      Enum.map(TrafficSemaphores.semaphores, fn (s) -> [
        %{ action: "TurnGreen(#{inspect s})", condition: turn_green_condition(variables, s), transition: fn (variables) -> turn_green(variables, s) end },
        %{ action: "TurnYellow(#{inspect s})", condition: turn_yellow_condition(variables, s), transition: fn (variables) -> turn_yellow(variables, s) end },
        %{ action: "TurnRed(#{inspect s})", condition: turn_red_condition(variables, s), transition: fn (variables) -> turn_red(variables, s) end }
      ] end
      )
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

