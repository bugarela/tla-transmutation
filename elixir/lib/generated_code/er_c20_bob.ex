defmodule ERC20_bob do
  require Oracle

  import ERC20
  @amounts "<value for AMOUNTS>"
  def amounts, do: @amounts


  @addr "<value for ADDR>"
  def addr, do: @addr



  def next(variables) do
    Enum.filter(
      List.flatten([
      Enum.map(@addr, fn (toAddr) -> [
        Enum.map(@amounts, fn (value) -> [
          %{ action: "SubmitTransfer(bob_OF_ADDR, #{inspect toAddr}, #{inspect value})", condition: submit_transfer_condition(variables, "bob_OF_ADDR", toAddr, value), state: submit_transfer(variables, "bob_OF_ADDR", toAddr, value) }
        ] end
        )
      ] end
      ),
      Enum.map(@addr, fn (fromAddr) -> [
        Enum.map(@addr, fn (toAddr) -> [
          Enum.map(@amounts, fn (value) -> [
            %{ action: "SubmitTransferFrom(bob_OF_ADDR, #{inspect fromAddr}, #{inspect toAddr}, #{inspect value})", condition: submit_transfer_from_condition(variables, "bob_OF_ADDR", fromAddr, toAddr, value), state: submit_transfer_from(variables, "bob_OF_ADDR", fromAddr, toAddr, value) }
          ] end
          )
        ] end
        )
      ] end
      ),
      Enum.map(@addr, fn (spender) -> [
        Enum.map(@amounts, fn (value) -> [
          %{ action: "SubmitApprove(bob_OF_ADDR, #{inspect spender}, #{inspect value})", condition: submit_approve_condition(variables, "bob_OF_ADDR", spender, value), state: submit_approve(variables, "bob_OF_ADDR", spender, value) }
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

