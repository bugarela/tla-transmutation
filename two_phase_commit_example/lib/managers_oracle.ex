defmodule ManagersOracle do
  def start do
    :global.register_name("oracle", self())

    spawn(ManagersOracle, :read, [])
    listen()
  end

  def listen do
    receive do
      {p, as} -> send p, {:ok, managers_choice(as)}
    end

    listen()
  end

  def managers_choice(actions) do
    enumerated_actions = actions |> Enum.with_index |> Enum.map(fn({x, i}) -> "#{i} => #{x}" end)

    send_choices(enumerated_actions, "r1")
    send_choices(enumerated_actions, "r2")
    show_transaction_manager_choices(enumerated_actions)

    receive do
      {:choice, i} -> IO.puts "From #{inspect actions}, oracle chose #{Enum.at(actions, i)}"; i
    end
  end

  def send_choices(as, id) do
    choices = Enum.filter(as, fn (a) -> a =~ id and a =~ "RM" end)

    send get_pid(id), {self(), choices}
  end

  def show_transaction_manager_choices(as) do
    transaction_manager_choices = Enum.filter(as, fn (a) -> a =~ "TM" end)

    IO.puts Enum.join(transaction_manager_choices, "\n")
    IO.puts ""
  end

  def read do
    {i, _} = Integer.parse(IO.gets("Escolha do Gerenciador de Transações: "))

    send :global.whereis_name("oracle"), {:choice, i}

    read()
  end

  def get_pid(id) do
    pid = :global.whereis_name(id)

    if pid == :undefined do
      get_pid(id)
    else
      pid
    end
  end
end
