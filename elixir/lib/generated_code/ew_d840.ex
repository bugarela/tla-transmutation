defmodule EWD840 do
  def shared_variables do
    [
      :tcolor,
      :tpos,
      :active,
    ]
  end
  require Oracle
  @n 3
  def n, do: @n


  def max_n(variables) do
    20
  end


  def color(variables) do
    MapSet.new(["white", "black"])
  end


  def const_init4(variables) do
    MapSet.member?(MapSet.new([4]), @n)
  end


  def const_init10(variables) do
    MapSet.member?(MapSet.new([10]), @n)
  end


  def const_init_all20(variables) do
    MapSet.member?(2..50, @n)
  end


  def nodes(variables) do
    MapSet.new(Enum.filter(0..max_n(variables), fn(i) -> i < @n end))
  end


  def initiate_probe_condition(variables) do
    Enum.all?([variables[:tpos] == 0, variables[:tcolor] == "black" or variables[:color][0] == "black"])
  end

  def initiate_probe(variables) do
    %{
      tpos: @n - 1,
      tcolor: "white",
      active: variables[:active],
      color: variables[:color]|>Map.put(0, "white")
    }
  end


  def pass_token_condition(variables, i) do
    Enum.all?([variables[:tpos] == i, not variables[:active][i] or variables[:color][i] == "black" or variables[:tcolor] == "black"])
  end

  def pass_token(variables, i) do
    %{
      tpos: i - 1,
      tcolor: (if variables[:color][i] == "black", do: "black", else: variables[:tcolor]),
      active: variables[:active],
      color: variables[:color]|>Map.put(i, "white")
    }
  end


  def send_msg_condition(variables, i, j) do
    variables[:active][i]
  end

  def send_msg(variables, i, j) do
    %{
      active: variables[:active]|>Map.put(j, true),
      color: variables[:color]|>Map.put(i, (if j > i, do: "black", else: variables[:color][i])),
      tpos: variables[:tpos],
      tcolor: variables[:tcolor]
    }
  end


  def deactivate_condition(variables, i) do
    variables[:active][i]
  end

  def deactivate(variables, i) do
    %{
      active: variables[:active]|>Map.put(i, false),
      color: variables[:color],
      tpos: variables[:tpos],
      tcolor: variables[:tcolor]
    }
  end


  def vars(variables) do
    {variables[:active], variables[:color], variables[:tpos], variables[:tcolor]}
  end


  def token_always_black(variables) do
    variables[:tcolor] == "black"
  end


  def termination_detected(variables) do
    variables[:tpos] == 0 and variables[:tcolor] == "white" and variables[:color][0] == "white" and not variables[:active][0]
  end


  # "NeverChangeColor": OperEx "GLOBALLY" [OperEx "STUTTER" [OperEx "UNCHANGED" [NameEx "color"],OperEx "OPER_APP" [NameEx "vars"]]]
  # "TerminationDetection": OperEx "IMPLIES" [OperEx "OPER_APP" [NameEx "terminationDetected"],OperEx "FORALL3" [NameEx "i",OperEx "OPER_APP" [NameEx "Nodes"],OperEx "NOT" [OperEx "FUN_APP" [NameEx "active",NameEx "i"]]]]
  # "Liveness": OperEx "LEADS_TO" [OperEx "FORALL3" [NameEx "i",OperEx "OPER_APP" [NameEx "Nodes"],OperEx "NOT" [OperEx "FUN_APP" [NameEx "active",NameEx "i"]]],OperEx "OPER_APP" [NameEx "terminationDetected"]]
  # "FalseLiveness": OperEx "LEADS_TO" [OperEx "FORALL3" [NameEx "i",OperEx "OPER_APP" [NameEx "Nodes"],OperEx "GLOBALLY" [OperEx "EVENTUALLY" [OperEx "NOT" [OperEx "FUN_APP" [NameEx "active",NameEx "i"]]]]],OperEx "OPER_APP" [NameEx "terminationDetected"]]
  # "Inv": OperEx "OR" [OperEx "LABEL" [OperEx "FORALL3" [NameEx "i",OperEx "OPER_APP" [NameEx "Nodes"],OperEx "IMPLIES" [OperEx "LT" [NameEx "tpos",NameEx "i"],OperEx "NOT" [OperEx "FUN_APP" [NameEx "active",NameEx "i"]]]],ValEx (TlaStr "P0")],OperEx "LABEL" [OperEx "EXISTS3" [NameEx "j",OperEx "OPER_APP" [NameEx "Nodes"],OperEx "IMPLIES" [OperEx "AND" [OperEx "LE" [ValEx (TlaInt 0),NameEx "j"],OperEx "LE" [NameEx "j",NameEx "tpos"]],OperEx "EQ" [OperEx "FUN_APP" [NameEx "color",NameEx "j"],ValEx (TlaStr "black")]]],ValEx (TlaStr "P1")],OperEx "LABEL" [OperEx "EQ" [NameEx "tcolor",ValEx (TlaStr "black")],ValEx (TlaStr "P2")]]
  # "SpecWFNext": OperEx "AND" [OperEx "AND" [OperEx "OPER_APP" [NameEx "Init"],OperEx "GLOBALLY" [OperEx "STUTTER" [OperEx "OPER_APP" [NameEx "Next"],OperEx "OPER_APP" [NameEx "vars"]]]],OperEx "WEAK_FAIRNESS" [OperEx "OPER_APP" [NameEx "vars"],OperEx "OPER_APP" [NameEx "Next"]]]
  # "CheckInductiveSpec": OperEx "AND" [OperEx "OPER_APP" [NameEx "Inv"],OperEx "GLOBALLY" [OperEx "STUTTER" [OperEx "OPER_APP" [NameEx "Next"],OperEx "OPER_APP" [NameEx "vars"]]]]

  def decide_action(oracle, variables, actions, step) do
    different_states = Enum.uniq(Enum.map(actions, fn(action) -> action[:transition].(variables) end))

    cond do
      Enum.count(different_states) == 1 ->
        Enum.at(different_states, 0)
      true ->
        send oracle, {:choose, self(), different_states}

       receive do
         {:ok, n} -> Enum.at(different_states, n)
         {:cancel} -> variables
         {:stop} -> exit(0)
       end
    end
  end

  def wait_lock(oracle) do
    send(oracle, {:lock, self()})
    receive do
      {:lock_acquired, state} -> IO.puts("Lock acquired"); {map, _} = Map.split(state, shared_variables); map
      {:already_locked, _} -> IO.puts("Lock refused"); Process.sleep(1000); wait_lock(oracle)
    end
  end
end

