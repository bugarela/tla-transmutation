defmodule JarrosDeAgua do
  @moduledoc """
   TypeOK == /\ jarro_pequeno \in 0..3
             /\ jarro_grande  \in 0..5
  """
  require Oracle
  # @oracle spawn(Oracle, :start, [])

  def enche_pequeno_condition(variables) do
    True
  end

  def enche_pequeno(variables) do
    %{
      jarro_pequeno: 3,
      jarro_grande: variables[:jarro_grande]
    }
  end

  def enche_grande_condition(variables) do
    True
  end

  def enche_grande(variables) do
    %{
      jarro_grande: 5,
      jarro_pequeno: variables[:jarro_pequeno]
    }
  end

  def esvazia_pequeno_condition(variables) do
    True
  end

  def esvazia_pequeno(variables) do
    %{
      jarro_pequeno: 0,
      jarro_grande: variables[:jarro_grande]
    }
  end

  def esvazia_grande_condition(variables) do
    True
  end

  def esvazia_grande(variables) do
    %{
      jarro_grande: 0,
      jarro_pequeno: variables[:jarro_pequeno]
    }
  end

  def pequeno_para_grande_condition(variables) do
    if variables[:jarro_grande] + variables[:jarro_pequeno] <= 5 do
      True
    else
      True
    end
  end

  def pequeno_para_grande(variables) do
    if variables[:jarro_grande] + variables[:jarro_pequeno] <= 5 do
      %{
        jarro_grande: variables[:jarro_grande] + variables[:jarro_pequeno],
        jarro_pequeno: 0
      }
    else
      %{
        jarro_grande: 5,
        jarro_pequeno: variables[:jarro_pequeno] - (5 - variables[:jarro_grande])
      }
    end
  end

  def grande_para_pequeno_condition(variables) do
    if variables[:jarro_grande] + variables[:jarro_pequeno] <= 3 do
      True
    else
      True
    end
  end

  def grande_para_pequeno(variables) do
    if variables[:jarro_grande] + variables[:jarro_pequeno] <= 3 do
      %{
        jarro_grande: 0,
        jarro_pequeno: variables[:jarro_grande] + variables[:jarro_pequeno]
      }
    else
      %{
        jarro_grande: variables[:jarro_pequeno] - (3 - variables[:jarro_grande]),
        jarro_pequeno: 3
      }
    end
  end

  def next(variables) do
    List.flatten([
      %{
        action: "EnchePequeno()",
        condition: enche_pequeno_condition(variables),
        state: enche_pequeno(variables)
      },
      %{
        action: "EncheGrande()",
        condition: enche_grande_condition(variables),
        state: enche_grande(variables)
      },
      %{
        action: "EsvaziaPequeno()",
        condition: esvazia_pequeno_condition(variables),
        state: esvazia_pequeno(variables)
      },
      %{
        action: "EsvaziaGrande()",
        condition: esvazia_grande_condition(variables),
        state: esvazia_grande(variables)
      },
      %{
        action: "PequenoParaGrande()",
        condition: pequeno_para_grande_condition(variables),
        state: pequeno_para_grande(variables)
      },
      %{
        action: "GrandeParaPequeno()",
        condition: grande_para_pequeno_condition(variables),
        state: grande_para_pequeno(variables)
      }
    ])
  end

  def main(oracle, variables, step) do
    IO.puts(inspect(variables))

    actions = next(variables)

    next_variables = decide_action(oracle, actions, step)
    send(oracle, {:notify, step, variables, next_variables})

    main(oracle, next_variables, step + 1)
  end

  def decide_action(oracle, actions, step) do
    possible_actions = Enum.filter(actions, fn action -> action[:condition] end)
    different_states = Enum.uniq_by(possible_actions, fn action -> action[:state] end)

    cond do
      Enum.count(different_states) == 1 -> Enum.at(possible_actions, 0)[:state]
      Enum.count(different_states) == 0 ->
        IO.puts("DEADLOCK")
        exit(0)
      true ->
        # actions_names = Enum.map(possible_actions, fn action -> action[:action] end)
        IO.inspect(different_states)
        send(oracle, {:choose, self(), step, possible_actions})

        n =
          receive do
          {:ok, n} -> n
          {:stop} -> exit(0)
        end

        Enum.at(possible_actions, n)[:state]
    end
  end
end
