defmodule TransactionCommit do
@moduledoc """
 This specification is explained in "Transaction Commit", Lecture 5 of
 the TLA+ Video Course.
*************************************************************************
 CONSTANT RM       \* The set of participating resource managers
 VARIABLE rmState  \* rmState[rm] is the state of resource manager r.
"""
  # ***********************************************************************
  #  The initial predicate.
  # ***********************************************************************
  @doc """

  """
  def can_commit_condition(variables) do
    Enum.member?(variables[:a], MapSet.new(["prepared", "committed"]))
  end

  def can_commit(variables) do
    variables

  end

  # ***********************************************************************
  #  True iff all RMs are in the "prepared" or "committed" state.
  # ***********************************************************************
  @doc """

  """
  def not_committed_condition(variables) do
    variables[:a] == "committed"
  end

  def not_committed(variables) do
    variables

  end

  # ***********************************************************************
  #  True iff no resource manager has decided to commit.
  # ***********************************************************************
  # *************************************************************************
  #  We now define the actions that may be performed by the RMs, and then
  #  define the complete next-state action of the specification to be the
  #  disjunction of the possible RM actions.
  # *************************************************************************
  @doc """

  """
  def prepare_condition(variables, r) do
    variables[:rm_state][r] == "working"
  end

  def prepare(variables, r) do
    %{
      rmState: Map.put(variables[:rm_state], r, "prepared")
    }
  end

  @doc """

  """
  def decide_condition(variables, r) do
    True

  end

  def decide(variables, r) do
    (
    conditions_and_actions = [
      {
        variables[:rm_state][r] == "prepared" and
        can_commit_condition(variables),
        Map.merge(
          %{
          rmState: Map.put(variables[:rm_state], r, "committed")
        },
          can_commit(variables))
      }, {
        Enum.member?(variables[:rm_state][r], MapSet.new(["working", "prepared"])) and
        not_committed_condition(variables),
        Map.merge(
          %{
          rmState: Map.put(variables[:rm_state], r, "aborted")
        },
          not_committed(variables))
      }
    ]
    possible_states = for {condition, action} <- conditions_and_actions,
    into: MapSet.new,
    do: if condition, do: action, else: nil

    possible_states = MapSet.delete(possible_states, nil)

    if MapSet.size(possible_states) == 1 do
      Enum.head(MapSet.to_list(possible_states))
    else
      raise 'Not enough information to decide'
    end
    )
  end

  @doc """

  """
  def main(variables) do
  decide_condition(variables, r)
  decide(variables, r)
  end
end


TransactionCommit.main(%{
rmState: constants[:RM] |> Enum.map(fn (r) -> {r, "working"} end) |> Enum.into(%{})
})
