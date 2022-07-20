defmodule APAEWD840_node2 do
  require Oracle

  import APAEWD840
  @n "<value for N>"
  def n, do: @n



  def next(variables) do
    List.flatten([
      %{ action: "PassToken(Lit (Num 2))", condition: pass_token_condition(variables, 2), state: pass_token(variables, 2) },
      %{ action: "SendMsg(Lit (Num 2))", condition: send_msg_condition(variables, 2), state: send_msg(variables, 2) },
      %{ action: "Deactivate(Lit (Num 2))", condition: deactivate_condition(variables, 2), state: deactivate(variables, 2) }
    ])
  end

  def main(oracle, variables, step) do
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
end

