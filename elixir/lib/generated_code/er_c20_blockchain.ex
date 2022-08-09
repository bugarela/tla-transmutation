defmodule ERC20_blockchain do
  require Oracle

  import ERC20

  def next(variables) do
    Enum.filter(
      List.flatten([
      Enum.map(variables[:pending_transactions], fn (tx) -> [
        %{ action: "CommitTransfer(#{inspect tx})", condition: commit_transfer_condition(variables, tx), transition: fn (variables) -> commit_transfer(variables, tx) end }
      ] end
      ),
      Enum.map(variables[:pending_transactions], fn (tx) -> [
        %{ action: "CommitTransferFrom(#{inspect tx})", condition: commit_transfer_from_condition(variables, tx), transition: fn (variables) -> commit_transfer_from(variables, tx) end }
      ] end
      ),
      Enum.map(variables[:pending_transactions], fn (tx) -> [
        %{ action: "CommitApprove(#{inspect tx})", condition: commit_approve_condition(variables, tx), transition: fn (variables) -> commit_approve(variables, tx) end }
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

