defmodule ResourceManager do
  def start(id) do
    Node.connect(:oracle@localhost)
    :global.register_name(id, self())

    spawn(ResourceManager, :read, [])
    listen(:undefined)
  end

  def listen(input) do
    receive do
      {p, as} -> show_options(as)
    end

    listen(input)
  end

  def read do
    {i, _} = Integer.parse(IO.gets("Escolha Gerenciador de Recursos: "))

    send :global.whereis_name("oracle"), {:choice, i}

    read()
  end

  def show_options(as) do
    IEx.Helpers.clear
    IO.puts Enum.join(as, "\n")
    IO.puts ""
  end
end

[arg1] = System.argv
ResourceManager.start(arg1)
