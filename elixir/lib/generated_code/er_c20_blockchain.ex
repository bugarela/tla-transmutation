defmodule ERC20_blockchain do
  require Oracle

  import ERC20
  @amounts "<value for AMOUNTS>"
  def amounts, do: @amounts


  @addr "<value for ADDR>"
  def addr, do: @addr



  def next(variables) do
    Enum.filter(
      List.flatten([
      Enum.map(variables[:pending_transactions], fn (tx) -> [
        %{ action: "CommitTransfer(#{inspect tx})", condition: commit_transfer_condition(variables, tx), state: commit_transfer(variables, tx) }
      ] end
      ),
      Enum.map(variables[:pending_transactions], fn (tx) -> [
        %{ action: "CommitTransferFrom(#{inspect tx})", condition: commit_transfer_from_condition(variables, tx), state: commit_transfer_from(variables, tx) }
      ] end
      ),
      Enum.map(variables[:pending_transactions], fn (tx) -> [
        %{ action: "CommitApprove(#{inspect tx})", condition: commit_approve_condition(variables, tx), state: commit_approve(variables, tx) }
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

