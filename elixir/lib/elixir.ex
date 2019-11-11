defmodule EfetivacaoEmDuasFases do
  require Oracle
  @oracle spawn(Oracle, :start, [])

  @gr MapSet.new(["r1", "r2"])
  def gr, do: @gr
  def gt_recebe_prepara_condition(variables, g) do
    variables[:estado_gt] == "inicio" and Enum.member?(variables[:msgs], %{ tipo: "EstouPreparado", gr: g })
  end

  def gt_recebe_prepara(variables, g) do
    %{
      g_rs_preparados: MapSet.put(variables[:g_rs_preparados], g),
      estado_gr: variables[:estado_gr],
      estado_gt: variables[:estado_gt],
      msgs: variables[:msgs]
    }
  end


  def gt_efetiva_condition(variables) do
    variables[:estado_gt] == "inicio" and variables[:g_rs_preparados] == @gr
  end

  def gt_efetiva(variables) do
    %{
      estado_gt: "termino",
      msgs: MapSet.put(variables[:msgs], %{ tipo: "Efetive" }),
      estado_gr: variables[:estado_gr],
      g_rs_preparados: variables[:g_rs_preparados]
    }
  end


  def gt_aborta_condition(variables) do
    variables[:estado_gt] == "inicio"
  end

  def gt_aborta(variables) do
    %{
      estado_gt: "termino",
      msgs: MapSet.put(variables[:msgs], %{ tipo: "Aborte" }),
      estado_gr: variables[:estado_gr],
      g_rs_preparados: variables[:g_rs_preparados]
    }
  end


  def gr_prepara_condition(variables, g) do
    variables[:estado_gr][g] == "trabalhando"
  end

  def gr_prepara(variables, g) do
    %{
      estado_gr: Map.put(variables[:estado_gr], g, "preparado"),
      msgs: MapSet.put(variables[:msgs], %{ tipo: "EstouPreparado", gr: g }),
      estado_gt: variables[:estado_gt],
      g_rs_preparados: variables[:g_rs_preparados]
    }
  end


  def gr_ecolhe_abortar_condition(variables, g) do
    variables[:estado_gr][g] == "trabalhando"
  end

  def gr_ecolhe_abortar(variables, g) do
    %{
      estado_gr: Map.put(variables[:estado_gr], g, "abortado"),
      estado_gt: variables[:estado_gt],
      g_rs_preparados: variables[:g_rs_preparados],
      msgs: variables[:msgs]
    }
  end


  def gr_recebe_msg_efetive_condition(variables, g) do
    Enum.member?(variables[:msgs], %{ tipo: "Efetive" })
  end

  def gr_recebe_msg_efetive(variables, g) do
    %{
      estado_gr: Map.put(variables[:estado_gr], g, "efetivado"),
      estado_gt: variables[:estado_gt],
      g_rs_preparados: variables[:g_rs_preparados],
      msgs: variables[:msgs]
    }
  end


  def gr_recebe_msg_aborte_condition(variables, g) do
    Enum.member?(variables[:msgs], %{ tipo: "Aborte" })
  end

  def gr_recebe_msg_aborte(variables, g) do
    %{
      estado_gr: Map.put(variables[:estado_gr], g, "abortado"),
      estado_gt: variables[:estado_gt],
      g_rs_preparados: variables[:g_rs_preparados],
      msgs: variables[:msgs]
    }
  end


  def main(variables) do
    IO.puts (inspect variables)

    main(
      decide_action(
        List.flatten([
          %{ action: "GTEfetiva()", condition: gt_efetiva_condition(variables), state: gt_efetiva(variables) },
          %{ action: "GTAborta()", condition: gt_aborta_condition(variables), state: gt_aborta(variables) },
          Enum.map(@gr, fn (g) -> [
            %{ action: "GTRecebePrepara(#{inspect g})", condition: gt_recebe_prepara_condition(variables, g), state: gt_recebe_prepara(variables, g) },
            %{ action: "GRPrepara(#{inspect g})", condition: gr_prepara_condition(variables, g), state: gr_prepara(variables, g) },
            %{ action: "GREcolheAbortar(#{inspect g})", condition: gr_ecolhe_abortar_condition(variables, g), state: gr_ecolhe_abortar(variables, g) },
            %{ action: "GRRecebeMsgEfetive(#{inspect g})", condition: gr_recebe_msg_efetive_condition(variables, g), state: gr_recebe_msg_efetive(variables, g) },
            %{ action: "GRRecebeMsgAborte(#{inspect g})", condition: gr_recebe_msg_aborte_condition(variables, g), state: gr_recebe_msg_aborte(variables, g) }
          ] end
          )
        ])
      )
    )
  end

  def decide_action(actions) do
    possible_actions = Enum.filter(actions, fn(action) -> action[:condition] end)
    different_states = Enum.uniq_by(possible_actions, fn(action) -> action[:state] end)

    if Enum.count(different_states) == 1 do
      IO.puts "Model decided: #{inspect Enum.at(possible_actions, 0)[:action]}"
      Enum.at(possible_actions, 0)[:state]
    else
      actions_names = Enum.map(possible_actions, fn(action) -> action[:action] end)
      send @oracle, {self(), actions_names}

      n = receive do
        {:ok, n} -> n
      end

      Enum.at(possible_actions, n)[:state]
    end
  end
end

IO.gets("start? ")
EfetivacaoEmDuasFases.main(
  %{
    estado_gr: EfetivacaoEmDuasFases.gr |> Enum.map(fn (g) -> {g, "trabalhando"} end) |> Enum.into(%{  }),
    estado_gt: "inicio",
    g_rs_preparados: MapSet.new([]),
    msgs: MapSet.new([])
  }
)
