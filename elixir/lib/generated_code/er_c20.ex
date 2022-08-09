defmodule ERC20 do
  def shared_variables do
    [
      :pending_transactions,
      :last_tx,
      :next_tx_id,
      :balance_of,
      :allowance,
    ]
  end
  require Oracle
  @amounts MapSet.new([0, 1, 2, 3, 98, 100, 102])
  def amounts, do: @amounts


  @addr MapSet.new(["Alice_OF_ADDR", "Bob_OF_ADDR", "Eve_OF_ADDR"])
  def addr, do: @addr


  def submit_transfer_condition(variables, _sender, _toAddr, _value) do
    new_tx = fn(variables) -> %{ "id" => variables[:next_tx_id], "tag" => "transfer", "fail" => false, "sender" => _sender, "toAddr" => _toAddr, "value" => _value }end
    Enum.all?([true])
  end

  def submit_transfer(variables, _sender, _toAddr, _value) do
    new_tx = fn(variables) -> %{ "id" => variables[:next_tx_id], "tag" => "transfer", "fail" => false, "sender" => _sender, "toAddr" => _toAddr, "value" => _value }end
    %{
      pending_transactions: MapSet.put(variables[:pending_transactions], new_tx.(variables)),
      last_tx: %{ "id" => 0, "tag" => "None", "fail" => false },
      next_tx_id: variables[:next_tx_id] + 1,
      balance_of: variables[:balance_of],
      allowance: variables[:allowance]
    }
  end


  def commit_transfer_condition(variables, _tx) do
    fail = fn(variables) -> _tx["value"] < 0 or _tx["value"] > variables[:balance_of][_tx["sender"]] or _tx["sender"] == _tx["toAddr"]end
    Enum.all?([_tx["tag"] == "transfer", (if fail.(variables), do: false, else: true)])
  end

  def commit_transfer(variables, _tx) do
    fail = fn(variables) -> _tx["value"] < 0 or _tx["value"] > variables[:balance_of][_tx["sender"]] or _tx["sender"] == _tx["toAddr"]end
    Map.merge(
      %{
      pending_transactions: MapSet.difference(variables[:pending_transactions], MapSet.new([_tx])),
      last_tx: _tx|>Map.put("fail", fail.(variables))
    },
      (if fail.(variables), do: %{
        balance_of: variables[:balance_of],
        allowance: variables[:allowance],
        next_tx_id: variables[:next_tx_id]
      }, else: %{
        balance_of: variables[:balance_of]|>Map.put(_tx["sender"], (variables[:balance_of][_tx["sender"]]) - (_tx["value"]))|>Map.put(_tx["toAddr"], (variables[:balance_of][_tx["toAddr"]]) + (_tx["value"])),
        allowance: variables[:allowance],
        next_tx_id: variables[:next_tx_id]
      }))
  end


  def submit_transfer_from_condition(variables, _sender, _fromAddr, _toAddr, _value) do
    new_tx = fn(variables) -> %{ "id" => variables[:next_tx_id], "tag" => "transferFrom", "fail" => false, "sender" => _sender, "fromAddr" => _fromAddr, "toAddr" => _toAddr, "value" => _value }end
    Enum.all?([true])
  end

  def submit_transfer_from(variables, _sender, _fromAddr, _toAddr, _value) do
    new_tx = fn(variables) -> %{ "id" => variables[:next_tx_id], "tag" => "transferFrom", "fail" => false, "sender" => _sender, "fromAddr" => _fromAddr, "toAddr" => _toAddr, "value" => _value }end
    %{
      pending_transactions: MapSet.put(variables[:pending_transactions], new_tx.(variables)),
      last_tx: %{ "id" => 0, "tag" => "None", "fail" => false },
      next_tx_id: variables[:next_tx_id] + 1,
      balance_of: variables[:balance_of],
      allowance: variables[:allowance]
    }
  end


  def commit_transfer_from_condition(variables, _tx) do
    fail = fn(variables) -> _tx["value"] < 0 or _tx["value"] > variables[:balance_of][_tx["fromAddr"]] or _tx["value"] > variables[:allowance][{_tx["fromAddr"], _tx["sender"]}] or _tx["fromAddr"] == _tx["toAddr"]end
    Enum.all?([_tx["tag"] == "transferFrom", (if fail.(variables), do: false, else: true)])
  end

  def commit_transfer_from(variables, _tx) do
    fail = fn(variables) -> _tx["value"] < 0 or _tx["value"] > variables[:balance_of][_tx["fromAddr"]] or _tx["value"] > variables[:allowance][{_tx["fromAddr"], _tx["sender"]}] or _tx["fromAddr"] == _tx["toAddr"]end
    Map.merge(
      %{
      pending_transactions: MapSet.difference(variables[:pending_transactions], MapSet.new([_tx])),
      last_tx: _tx|>Map.put("fail", fail.(variables))
    },
      (if fail.(variables), do: %{
        balance_of: variables[:balance_of],
        allowance: variables[:allowance],
        next_tx_id: variables[:next_tx_id]
      }, else: %{
        balance_of: variables[:balance_of]|>Map.put(_tx["fromAddr"], (variables[:balance_of][_tx["fromAddr"]]) - (_tx["value"]))|>Map.put(_tx["toAddr"], (variables[:balance_of][_tx["toAddr"]]) + (_tx["value"])),
        allowance: variables[:allowance]|>Map.put({_tx["fromAddr"], _tx["sender"]}, (variables[:allowance][{_tx["fromAddr"], _tx["sender"]}]) - (_tx["value"])),
        next_tx_id: variables[:next_tx_id]
      }))
  end


  def submit_approve_condition(variables, _sender, _spender, _value) do
    new_tx = fn(variables) -> %{ "id" => variables[:next_tx_id], "tag" => "approve", "fail" => false, "sender" => _sender, "spender" => _spender, "value" => _value }end
    Enum.all?([true])
  end

  def submit_approve(variables, _sender, _spender, _value) do
    new_tx = fn(variables) -> %{ "id" => variables[:next_tx_id], "tag" => "approve", "fail" => false, "sender" => _sender, "spender" => _spender, "value" => _value }end
    %{
      pending_transactions: MapSet.put(variables[:pending_transactions], new_tx.(variables)),
      last_tx: %{ "id" => 0, "tag" => "None", "fail" => false },
      next_tx_id: variables[:next_tx_id] + 1,
      balance_of: variables[:balance_of],
      allowance: variables[:allowance]
    }
  end


  def commit_approve_condition(variables, _tx) do
    fail = fn(variables) -> _tx["value"] < 0 or _tx["sender"] == _tx["spender"]end
    Enum.all?([_tx["tag"] == "approve", (if fail.(variables), do: false, else: true)])
  end

  def commit_approve(variables, _tx) do
    fail = fn(variables) -> _tx["value"] < 0 or _tx["sender"] == _tx["spender"]end
    Map.merge(
      %{
      pending_transactions: MapSet.difference(variables[:pending_transactions], MapSet.new([_tx])),
      balance_of: variables[:balance_of],
      next_tx_id: variables[:next_tx_id],
      last_tx: _tx|>Map.put("fail", fail.(variables))
    },
      (if fail.(variables), do: %{
        allowance: variables[:allowance]
      }, else: %{
        allowance: variables[:allowance]|>Map.put({_tx["sender"], _tx["spender"]}, _tx["value"])
      }))
  end



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

