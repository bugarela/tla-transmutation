defmodule Oracle do
  def start do
    :global.register_name("oracle", self())

    spawn(Oracle, :read, [])
    listen()
  end

  def listen do
    IO.puts "Oracle at [#{inspect self()}] is listening"

    receive do
      {p, as} -> send p, {:ok, input_option(as)}
    end

    listen()
  end

  def input_option(actions) do
    enumerated_actions = actions |> Enum.with_index |> Enum.map(fn({x, i}) -> "#{i} => #{x}" end)
    IO.puts (inspect enumerated_actions)

    receive do
      {:choice, i} -> i
    end
  end

  def read do
    {i, _} = Integer.parse(IO.gets("Next Action: "))

    send :global.whereis_name("oracle"), {:choice, i}

    read()
  end
end
