defmodule TwoPhaseCommit do
  @moduledoc """
  *************************************************************************
   This specification is discussed in "Two-Phase Commit", Lecture 6 of the
   TLA+ Video Course.  It describes the Two-Phase Commit protocol, in
   which a transaction manager (TM) coordinates the resource managers
   (RMs) to implement the Transaction Commit specification of module
   TCommit.  In this specification, RMs spontaneously issue Prepared
   messages.  We ignore the Prepare messages that the TM can send to the
   RMs.
   
   For simplicity, we also eliminate Abort messages sent by an RM when it
   decides to abort.  Such a message would cause the TM to abort the
   transaction, an event represented here by the TM spontaneously deciding
   to abort.
  *************************************************************************
  """
  require ManagersOracle
  @oracle spawn(ManagersOracle, :start, [])

  @rm MapSet.new(["r1", "r2"])
  def rm, do: @rm


  # *********************************************************************
  #  In the protocol, processes communicate with one another by sending
  #  messages.  For simplicity, we represent message passing with the
  #  variable msgs whose value is the set of all messages that have been
  #  sent.  A message is sent by adding it to the set msgs.  An action
  #  that, in an implementation, would be enabled by the receipt of a
  #  certain message is here enabled by the presence of that message in
  #  msgs.  For simplicity, messages are never removed from msgs.  This
  #  allows a single message to be received by multiple receivers.
  #  Receipt of the same message twice is therefore allowed; but in this
  #  particular protocol, that's not a problem.
  # *********************************************************************
  #  Messages ==
  # ***********************************************************************
  #  The set of all possible messages.  Messages of type "Prepared" are
  #  sent from the RM indicated by the message's rm field to the TM.
  #  Messages of type "Commit" and "Abort" are broadcast by the TM, to be
  #  received by all RMs.  The set msgs contains just a single copy of
  #  such a message.
  # ***********************************************************************
  #  [type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]
  #  TPTypeOK ==
  # ***********************************************************************
  #  The type-correctness invariant
  # ***********************************************************************
  #  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  #  /\ tmState \in {"init", "done"}
  #  /\ tmPrepared \subseteq RM
  #  /\ msgs \subseteq Messages
  # *************************************************************************
  #  We now define the actions that may be performed by the processes, first
  #  the TM's actions, then the RMs' actions.
  # *************************************************************************
  @doc """
  ***********************************************************************
   The TM receives a "Prepared" message from resource manager r.  We
   could add the additional enabling condition r \notin tmPrepared,
   which disables the action if the TM has already received this
   message.  But there is no need, because in that case the action has
   no effect; it leaves the state unchanged.
  ***********************************************************************
  """
  def tm_rcv_prepared_condition(variables, r) do
    variables[:tm_state] == "init" and Enum.member?(variables[:msgs], %{ type: "Prepared", rm: r })
  end

  def tm_rcv_prepared(variables, r) do
    %{
      tm_prepared: MapSet.put(variables[:tm_prepared], r),
      rm_state: variables[:rm_state],
      tm_state: variables[:tm_state],
      msgs: variables[:msgs]
    }
  end


  @doc """
  ***********************************************************************
   The TM commits the transaction; enabled iff the TM is in its initial
   state and every RM has sent a "Prepared" message.
  ***********************************************************************
  """
  def tm_commit_condition(variables) do
    variables[:tm_state] == "init" and variables[:tm_prepared] == @rm
  end

  def tm_commit(variables) do
    %{
      tm_state: "done",
      msgs: MapSet.put(variables[:msgs], %{ type: "Commit" }),
      rm_state: variables[:rm_state],
      tm_prepared: variables[:tm_prepared]
    }
  end


  @doc """
  ***********************************************************************
   The TM spontaneously aborts the transaction.
  ***********************************************************************
  """
  def tm_abort_condition(variables) do
    variables[:tm_state] == "init"
  end

  def tm_abort(variables) do
    %{
      tm_state: "done",
      msgs: MapSet.put(variables[:msgs], %{ type: "Abort" }),
      rm_state: variables[:rm_state],
      tm_prepared: variables[:tm_prepared]
    }
  end


  @doc """
  ***********************************************************************
   Resource manager r prepares.
  ***********************************************************************
  """
  def rm_prepare_condition(variables, r) do
    variables[:rm_state][r] == "working"
  end

  def rm_prepare(variables, r) do
    %{
      rm_state: Map.put(variables[:rm_state], r, "prepared"),
      msgs: MapSet.put(variables[:msgs], %{ type: "Prepared", rm: r }),
      tm_state: variables[:tm_state],
      tm_prepared: variables[:tm_prepared]
    }
  end


  @doc """
  ***********************************************************************
   Resource manager r spontaneously decides to abort.  As noted above, r
   does not send any message in our simplified spec.
  ***********************************************************************
  """
  def rm_choose_to_abort_condition(variables, r) do
    variables[:rm_state][r] == "working"
  end

  def rm_choose_to_abort(variables, r) do
    %{
      rm_state: Map.put(variables[:rm_state], r, "aborted"),
      tm_state: variables[:tm_state],
      tm_prepared: variables[:tm_prepared],
      msgs: variables[:msgs]
    }
  end


  @doc """
  ***********************************************************************
   Resource manager r is told by the TM to commit.
  ***********************************************************************
  """
  def rm_rcv_commit_msg_condition(variables, r) do
    Enum.member?(variables[:msgs], %{ type: "Commit" })
  end

  def rm_rcv_commit_msg(variables, r) do
    %{
      rm_state: Map.put(variables[:rm_state], r, "committed"),
      tm_state: variables[:tm_state],
      tm_prepared: variables[:tm_prepared],
      msgs: variables[:msgs]
    }
  end


  @doc """
  ***********************************************************************
   Resource manager r is told by the TM to abort.
  ***********************************************************************
  """
  def rm_rcv_abort_msg_condition(variables, r) do
    Enum.member?(variables[:msgs], %{ type: "Abort" })
  end

  def rm_rcv_abort_msg(variables, r) do
    %{
      rm_state: Map.put(variables[:rm_state], r, "aborted"),
      tm_state: variables[:tm_state],
      tm_prepared: variables[:tm_prepared],
      msgs: variables[:msgs]
    }
  end


  # *************************************************************************
  #  The material below this point is not discussed in Video Lecture 6.  It
  #  will be explained in Video Lecture 8.
  # *************************************************************************
  #  TPSpec == TPInit /\ [][TPNext]_<<rmState, tmState, tmPrepared, msgs>>
  # ***********************************************************************
  #  The complete spec of the Two-Phase Commit protocol.
  # ***********************************************************************
  # ***********************************************************************
  #  This theorem asserts that the type-correctness predicate TPTypeOK is
  #  an invariant of the specification.
  # ***********************************************************************
  # *************************************************************************
  #  We now assert that the Two-Phase Commit protocol implements the
  #  Transaction Commit protocol of module TCommit.  The following statement
  #  imports all the definitions from module TCommit into the current
  #  module.
  # *************************************************************************
  # ***********************************************************************
  #  This theorem asserts that the specification TPSpec of the Two-Phase
  #  Commit protocol implements the specification TCSpec of the
  #  Transaction Commit protocol.
  # ***********************************************************************
  # *************************************************************************
  #  The two theorems in this module have been checked with TLC for six
  #  RMs, a configuration with 50816 reachable states, in a little over a
  #  minute on a 1 GHz PC.
  # *************************************************************************
  def main(variables) do
    IEx.Helpers.clear
    IO.puts (inspect(variables, pretty: true))

    main(
      decide_action(
        List.flatten([
          %{ action: "TMCommit()", condition: tm_commit_condition(variables), state: tm_commit(variables) },
          %{ action: "TMAbort()", condition: tm_abort_condition(variables), state: tm_abort(variables) },
          Enum.map(@rm, fn (r) -> [
            %{ action: "TMRcvPrepared(#{r})", condition: tm_rcv_prepared_condition(variables, r), state: tm_rcv_prepared(variables, r) },
            %{ action: "RMPrepare(#{r})", condition: rm_prepare_condition(variables, r), state: rm_prepare(variables, r) },
            %{ action: "RMChooseToAbort(#{r})", condition: rm_choose_to_abort_condition(variables, r), state: rm_choose_to_abort(variables, r) },
            %{ action: "RMRcvCommitMsg(#{r})", condition: rm_rcv_commit_msg_condition(variables, r), state: rm_rcv_commit_msg(variables, r) },
            %{ action: "RMRcvAbortMsg(#{r})", condition: rm_rcv_abort_msg_condition(variables, r), state: rm_rcv_abort_msg(variables, r) }
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

IO.gets("start?")
TwoPhaseCommit.main(
  # ***********************************************************************
  #  The initial predicate.
  # ***********************************************************************
  %{
    rm_state: TwoPhaseCommit.rm |> Enum.map(fn (r) -> {r, "working"} end) |> Enum.into(%{  }),
    tm_state: "init",
    tm_prepared: MapSet.new([]),
    msgs: MapSet.new([])
  }
)
