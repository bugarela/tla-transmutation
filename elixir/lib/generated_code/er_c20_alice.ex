defmodule ERC20_alice do
  require Oracle

  import ERC20

  def next(variables) do
    Enum.filter(
      List.flatten([
      Enum.map(ERC20.addr, fn (toAddr) -> [
        Enum.map(ERC20.amounts, fn (value) -> [
          %{ action: "SubmitTransfer(alice_OF_ADDR, #{inspect toAddr}, #{inspect value})", condition: submit_transfer_condition(variables, "alice_OF_ADDR", toAddr, value), state: submit_transfer(variables, "alice_OF_ADDR", toAddr, value) }
        ] end
        )
      ] end
      ),
      Enum.map(ERC20.addr, fn (fromAddr) -> [
        Enum.map(ERC20.addr, fn (toAddr) -> [
          Enum.map(ERC20.amounts, fn (value) -> [
            %{ action: "SubmitTransferFrom(alice_OF_ADDR, #{inspect fromAddr}, #{inspect toAddr}, #{inspect value})", condition: submit_transfer_from_condition(variables, "alice_OF_ADDR", fromAddr, toAddr, value), state: submit_transfer_from(variables, "alice_OF_ADDR", fromAddr, toAddr, value) }
          ] end
          )
        ] end
        )
      ] end
      ),
      Enum.map(ERC20.addr, fn (spender) -> [
        Enum.map(ERC20.amounts, fn (value) -> [
          %{ action: "SubmitApprove(alice_OF_ADDR, #{inspect spender}, #{inspect value})", condition: submit_approve_condition(variables, "alice_OF_ADDR", spender, value), state: submit_approve(variables, "alice_OF_ADDR", spender, value) }
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

    IO.puts(inspect(variables))
    actions = next(variables)

    next_variables = decide_action(oracle, variables, actions, step)
    send(oracle, {:notify, step, variables, next_variables})
    Process.sleep(2000)

    main(oracle, next_variables, step + 1)
  end
end

