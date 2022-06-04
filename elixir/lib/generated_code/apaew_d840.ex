defmodule ApaewD840 do
  require Oracle
  @oracle spawn(Oracle, :start, [])

  @n "<value for N>"
  def n, do: @n


  def max_n_condition(variables) do
    20
  end


  def color_condition(variables) do
    MapSet.new(["white", "black"])
  end


  def const_init4_condition(variables) do
    MapSet.member?(MapSet.new([4]), @n)
  end


  def const_init10_condition(variables) do
    MapSet.member?(MapSet.new([10]), @n)
  end


  def const_init_all20_condition(variables) do
    MapSet.member?(2..50, @n)
  end


  def nodes_condition(variables) do
    Enum.filter(0..max_n_condition(variables), fn(i) -> i < @n end)
  end


  def initiate_probe_condition(variables) do
    Enum.all?([variables[:tpos] == 0, variables[:tcolor] == "black" or variables[:color][0] == "black"])
  end

  def initiate_probe(variables) do
    %{
      tpos: @n - 1,
      tcolor: "white",
      active: variables[:active],
      color: Map.put(variables[:color], {0}, "white")
    }
  end


  def pass_token_condition(variables) do
    Enum.all?([variables[:tpos] == i(variables), not variables[:active][i(variables)] or variables[:color][i(variables)] == "black" or variables[:tcolor] == "black"])
  end

  def pass_token(variables) do
    %{
      tpos: i(variables) - 1,
      tcolor: if variables[:color][i(variables)] == "black", do: "black", else: variables[:tcolor],
      active: variables[:active],
      color: Map.put(variables[:color], {i(variables)}, "white")
    }
  end


  def deactivate_condition(variables) do
    variables[:active][i(variables)]
  end

  def deactivate(variables) do
    %{
      active: Map.put(variables[:active], {i(variables)}, false)
      ,
      color: variables[:color],
      tpos: variables[:tpos],
      tcolor: variables[:tcolor]
    }
  end


  def vars_condition(variables) do
    {variables[:active], variables[:color], variables[:tpos], variables[:tcolor]}
  end


  def token_always_black_condition(variables) do
    variables[:tcolor] == "black"
  end


  def termination_detected_condition(variables) do
    variables[:tpos] == 0 and variables[:tcolor] == "white" and variables[:color][0] == "white" and not variables[:active][0]
  end


  def system_condition(variables) do
    initiate_probe_condition(variables) or Enum.any?(MapSet.difference?(nodes_condition(variables), MapSet.new([0])), fn(i) -> pass_token_condition(variables, i) end)
  end


  def send_msg_condition(variables) do
    Enum.all?([variables[:active][i(variables)], Enum.any?(MapSet.difference?(nodes_condition(variables), MapSet.new([i(variables)])), fn (j) ->trueend
    )])
  end

  def send_msg(variables) do
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
              color: Map.put(variables[:color], {i(variables)}, if j(variables) > i(variables), do: "black", else: variables[:color][i(variables)])
            } }
          ])
        )
      ))
  end


  # OperEx "GLOBALLY" [OperEx "STUTTER" [OperEx "UNCHANGED" [NameEx "color"],OperEx "OPER_APP" [NameEx "vars"]]]
  # OperEx "IMPLIES" [OperEx "OPER_APP" [NameEx "terminationDetected"],OperEx "FORALL3" [NameEx "i",OperEx "OPER_APP" [NameEx "Nodes"],OperEx "NOT" [OperEx "FUN_APP" [NameEx "active",NameEx "i"]]]]
  # OperEx "LEADS_TO" [OperEx "FORALL3" [NameEx "i",OperEx "OPER_APP" [NameEx "Nodes"],OperEx "NOT" [OperEx "FUN_APP" [NameEx "active",NameEx "i"]]],OperEx "OPER_APP" [NameEx "terminationDetected"]]
  # OperEx "LEADS_TO" [OperEx "FORALL3" [NameEx "i",OperEx "OPER_APP" [NameEx "Nodes"],OperEx "GLOBALLY" [OperEx "EVENTUALLY" [OperEx "NOT" [OperEx "FUN_APP" [NameEx "active",NameEx "i"]]]]],OperEx "OPER_APP" [NameEx "terminationDetected"]]
  # OperEx "OR" [OperEx "LABEL" [OperEx "FORALL3" [NameEx "i",OperEx "OPER_APP" [NameEx "Nodes"],OperEx "IMPLIES" [OperEx "LT" [NameEx "tpos",NameEx "i"],OperEx "NOT" [OperEx "FUN_APP" [NameEx "active",NameEx "i"]]]],ValEx (TlaStr "P0")],OperEx "LABEL" [OperEx "EXISTS3" [NameEx "j",OperEx "OPER_APP" [NameEx "Nodes"],OperEx "IMPLIES" [OperEx "AND" [OperEx "LE" [ValEx (TlaInt 0),NameEx "j"],OperEx "LE" [NameEx "j",NameEx "tpos"]],OperEx "EQ" [OperEx "FUN_APP" [NameEx "color",NameEx "j"],ValEx (TlaStr "black")]]],ValEx (TlaStr "P1")],OperEx "LABEL" [OperEx "EQ" [NameEx "tcolor",ValEx (TlaStr "black")],ValEx (TlaStr "P2")]]
  def environment_condition(variables) do
    Enum.any?(nodes_condition(variables), fn(i) -> send_msg_condition(variables, i) or deactivate_condition(variables, i) end)
  end


  # OperEx "IMPLIES" [OperEx "EVENTUALLY" [OperEx "GLOBALLY" [OperEx "STUTTER" [OperEx "FORALL3" [NameEx "i",OperEx "OPER_APP" [NameEx "Nodes"],OperEx "NOT" [OperEx "OPER_APP" [NameEx "SendMsg",NameEx "i"]]],OperEx "OPER_APP" [NameEx "vars"]]]],OperEx "EVENTUALLY" [OperEx "FORALL3" [NameEx "i",OperEx "OPER_APP" [NameEx "Nodes"],OperEx "NOT" [OperEx "FUN_APP" [NameEx "active",NameEx "i"]]]]]
  # OperEx "AND" [OperEx "AND" [OperEx "OPER_APP" [NameEx "Init"],OperEx "GLOBALLY" [OperEx "STUTTER" [OperEx "OPER_APP" [NameEx "Next"],OperEx "OPER_APP" [NameEx "vars"]]]],OperEx "WEAK_FAIRNESS" [OperEx "OPER_APP" [NameEx "vars"],OperEx "OPER_APP" [NameEx "System"]]]
  # OperEx "AND" [OperEx "AND" [OperEx "OPER_APP" [NameEx "Init"],OperEx "GLOBALLY" [OperEx "STUTTER" [OperEx "OPER_APP" [NameEx "Next"],OperEx "OPER_APP" [NameEx "vars"]]]],OperEx "WEAK_FAIRNESS" [OperEx "OPER_APP" [NameEx "vars"],OperEx "OPER_APP" [NameEx "Next"]]]
  # OperEx "AND" [OperEx "OPER_APP" [NameEx "Inv"],OperEx "GLOBALLY" [OperEx "STUTTER" [OperEx "OPER_APP" [NameEx "Next"],OperEx "OPER_APP" [NameEx "vars"]]]]
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
