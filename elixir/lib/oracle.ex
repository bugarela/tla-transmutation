defmodule Oracle do
  def start do
    :global.register_name("oracle", self())

    spawn(Oracle, :read, [])
    listen()
  end

  def listen do
    IO.puts "[#{inspect self}] is listening"

    receive do
      {p, as} -> send p, {:ok, escolha_gerenciadores(as)}
    end
    listen()
  end

  def escolha_gerenciadores(as) do
    enumerated_as = as |> Enum.with_index |> Enum.map(fn({x, i}) -> "#{i} => #{x}" end)

    envia_escolhas(enumerated_as, "r1")
    envia_escolhas(enumerated_as, "r2")
    mostra_escolhas_oraculo(enumerated_as)

    receive do
      {:escolha, i} -> IO.puts "From #{inspect as}, oracle chose #{Enum.at(as, i)}"; i
    end
  end

  def envia_escolhas(as, id) do
    escolhas_para_gerenciador = Enum.filter(as, fn (a) -> a =~ id and a =~ "GR" end)
    pid = :global.whereis_name(id)

    send pid, {self(), escolhas_para_gerenciador}
  end

  def mostra_escolhas_oraculo(as) do
    escolhas_gerenciador_transicoes = Enum.filter(as, fn (a) -> a =~ "GT" end)
    IO.puts (inspect escolhas_gerenciador_transicoes)
  end

  def read do
    {i, _} = Integer.parse(IO.gets("Escolha do Gerenciador de Transações: "))
    send :global.whereis_name("oracle"), {:escolha, i}

    read()
  end
end
