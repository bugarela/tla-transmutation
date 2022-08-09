defmodule ERC20_bob do
  require Oracle

  import ERC20

  def next(variables) do
    Enum.filter(
      List.flatten([
      Enum.map(ERC20.addr, fn (toAddr) -> [
        Enum.map(ERC20.amounts, fn (value) -> [
          %{ action: "SubmitTransfer(Bob_OF_ADDR, #{inspect toAddr}, #{inspect value})", condition: submit_transfer_condition(variables, "Bob_OF_ADDR", toAddr, value), transition: fn (variables) -> submit_transfer(variables, "Bob_OF_ADDR", toAddr, value) end }
        ] end
        )
      ] end
      ),
      Enum.map(ERC20.addr, fn (fromAddr) -> [
        Enum.map(ERC20.addr, fn (toAddr) -> [
          Enum.map(ERC20.amounts, fn (value) -> [
            %{ action: "SubmitTransferFrom(Bob_OF_ADDR, #{inspect fromAddr}, #{inspect toAddr}, #{inspect value})", condition: submit_transfer_from_condition(variables, "Bob_OF_ADDR", fromAddr, toAddr, value), transition: fn (variables) -> submit_transfer_from(variables, "Bob_OF_ADDR", fromAddr, toAddr, value) end }
          ] end
          )
        ] end
        )
      ] end
      ),
      Enum.map(ERC20.addr, fn (spender) -> [
        Enum.map(ERC20.amounts, fn (value) -> [
          %{ action: "SubmitApprove(Bob_OF_ADDR, #{inspect spender}, #{inspect value})", condition: submit_approve_condition(variables, "Bob_OF_ADDR", spender, value), transition: fn (variables) -> submit_approve(variables, "Bob_OF_ADDR", spender, value) end }
        ] end
        )
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

