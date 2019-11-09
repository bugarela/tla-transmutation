defmodule Oracle do
  def listen do
    IO.puts "[#{inspect self}] is listening"

    receive do
      {_, "Next", as} -> IO.puts (inspect as)
    end
    listen
  end
end
