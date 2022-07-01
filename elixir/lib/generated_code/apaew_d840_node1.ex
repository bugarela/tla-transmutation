defmodule ApaewD840 do
  require Oracle
  @oracle spawn(Oracle, :start, [])

  @n "<value for N>"
  def n, do: @n


  def pass_token_condition(variables, i) do
    Enum.all?([variables[:tpos] == i, not variables[:active][i] or variables[:color][i] == "black" or variables[:tcolor] == "black"])
  end

  def pass_token(variables, i) do
    %{
      tpos: i - 1,
      tcolor: if variables[:color][i] == "black", do: "black", else: variables[:tcolor],
      active: variables[:active],
      color: Map.put(variables[:color], {i}, "white")
    }
  end


  def deactivate_condition(variables, i) do
    variables[:active][i]
  end

  def deactivate(variables, i) do
    %{
      active: Map.put(variables[:active], {i}, false)
      ,
      color: variables[:color],
      tpos: variables[:tpos],
      tcolor: variables[:tcolor]
    }
  end


  def send_msg_condition(variables, i) do
    Enum.all?([variables[:active][i], Enum.any?(MapSet.difference?(nodes_condition(variables), MapSet.new([i])), fn (j) ->trueend
    )])
  end

  def send_msg(variables, i) do
    Map.merge(
      %{
      tpos: variables[:tpos],
      tcolor: variables[:tcolor]
    },
      (
        decide_action(
          List.flatten([
            %{ action: "ActionAnd [Primed \"active\" \(Except \"active\" [\(Tuple [Ref \"j\"\],Lit \(Boolean True\)\)\]\),Primed \"color\" \(Except \"color\" [\(Tuple [Ref \"i\"\],If \(Gt \(Ref \"j\"\) \(Ref \"i\"\)\) \(Lit \(Str \"black\"\)\) \(Index \(Ref \"color\"\) \(Ref \"i\"\)\)\)\]\)\]", condition: true, state: %{
              active: Map.put(variables[:active], {j(variables)}, true)
              ,
              color: Map.put(variables[:color], {i}, if j(variables) > i, do: "black", else: variables[:color][i])
            } }
          ])
        )
      ))
  end


  def main(variables) do
    IO.puts (inspect variables)

    main(%{})
  end

  def decide_action(actions) do
    possible_actions = Enum.filter(actions, fn(action) -> action[:condition] end)
    different_states = Enum.uniq_by(possible_actions, fn(action) -> action[:state] end)

    cond do
      Enum.count(different_states) == 1 ->
        Enum.at(possible_actions, 0)[:state]
      Enum.empty?(different_states) ->
        %{}
      true ->
        actions_names = Enum.map(possible_actions, fn(action) -> action[:action] end)
        send @oracle, {self(), actions_names}

        n = receive do
          {:ok, n} -> n
        end

        Enum.at(possible_actions, n)[:state]
    end
  end
end

ApaewD840.main(

  %{
    active: MapSet.new(nodes_condition(variables), fn(n) -> true end),
    color: MapSet.new(nodes_condition(variables), fn(n) -> "white" end),
    tpos: 0,
    tcolor: "black"
  }
)
