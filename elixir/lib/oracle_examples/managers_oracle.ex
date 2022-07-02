defmodule ManagersOracle do
  def start do
    :global.register_name("oracle", self())

    spawn(ManagersOracle, :read, [])
    listen()
  end

  def listen do
    receive do
      {:choose, p, _, as} -> send(p, {:ok, managers_choice(as)})
    end

    listen()
  end

  def managers_choice(actions) do
    enumerated_actions = actions |> Enum.with_index() |> Enum.map(fn {x, i} -> "#{i} => #{x}" end)

    send_choices(enumerated_actions, "r1")
    send_choices(enumerated_actions, "r2")
    show_transaction_manager_choices(enumerated_actions)

    receive do
      {:choice, i} ->
        IO.puts("From #{inspect(actions)}, oracle chose #{Enum.at(actions, i)}")
        i
    end
  end

  def send_choices(as, id) do
    choices = Enum.filter(as, fn a -> a =~ id and a =~ "GR" end)

    manager_pid = :global.whereis_name(id)
    send(manager_pid, {self(), choices})
  end

  def show_transaction_manager_choices(as) do
    transaction_manager_choices = Enum.filter(as, fn a -> a =~ "GT" end)

    IO.puts(inspect(transaction_manager_choices))
  end

  def read do
    {i, _} = Integer.parse(IO.gets("Escolha do Gerenciador de Transações: "))

    send(:global.whereis_name("oracle"), {:choice, i})

    read()
  end
end
