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
  @rm<value for RM>
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
    variables[:tm_state] == "init" and
    Enum.member?(%{type: "Prepared"}, %{rm: r}, variables[:msgs])
  end

  def tm_rcv_prepared(variables, r) do
    %{
      tmPrepared: MapSet.put(variables[:tm_prepared], r),
      rmState: variables[:rm_state],
      tmState: variables[:tm_state],
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
    variables[:tm_state] == "init" and
    variables[:tm_prepared] == constants[:RM]
  end

  def tm_commit(variables) do
    %{
      tmState: "done",
      msgs: MapSet.put(variables[:msgs], %{type: "Commit"}),
      rmState: variables[:rm_state],
      tmPrepared: variables[:tm_prepared]
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
      tmState: "done",
      msgs: MapSet.put(variables[:msgs], %{type: "Abort"}),
      rmState: variables[:rm_state],
      tmPrepared: variables[:tm_prepared]
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
      rmState: Map.put(variables[:rm_state], r, "prepared"),
      msgs: MapSet.put(variables[:msgs], %{type: "Prepared"}, %{rm: r}),
      tmState: variables[:tm_state],
      tmPrepared: variables[:tm_prepared]
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
      rmState: Map.put(variables[:rm_state], r, "aborted"),
      tmState: variables[:tm_state],
      tmPrepared: variables[:tm_prepared],
      msgs: variables[:msgs]
    }
  end

  @doc """
  ***********************************************************************
   Resource manager r is told by the TM to commit.                       
  ***********************************************************************
  """
  def rm_rcv_commit_msg_condition(variables, r) do
    Enum.member?(%{type: "Commit"}, variables[:msgs])
  end

  def rm_rcv_commit_msg(variables, r) do
    %{
      rmState: Map.put(variables[:rm_state], r, "committed"),
      tmState: variables[:tm_state],
      tmPrepared: variables[:tm_prepared],
      msgs: variables[:msgs]
    }
  end

  @doc """
  ***********************************************************************
   Resource manager r is told by the TM to abort.                        
  ***********************************************************************
  """
  def rm_rcv_abort_msg_condition(variables, r) do
    Enum.member?(%{type: "Abort"}, variables[:msgs])
  end

  def rm_rcv_abort_msg(variables, r) do
    %{
      rmState: Map.put(variables[:rm_state], r, "aborted"),
      tmState: variables[:tm_state],
      tmPrepared: variables[:tm_prepared],
      msgs: variables[:msgs]
    }
  end

  #  \/ \E r \in RM :
  #       TMRcvPrepared(r) \/ RMPrepare(r) \/ RMChooseToAbort(r)
  #         \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)
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
  @doc """

  """
  def main(variables) do
  (
  conditions_and_actions = [
    {
      tm_commit_condition(variables),
      tm_commit(variables)
    }, {
      tm_abort_condition(variables),
      tm_abort(variables)
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
end

# ***********************************************************************
#  The initial predicate.
# ***********************************************************************
TwoPhaseCommit.main(%{
rmState: constants[:RM] |> Enum.map(fn (r) -> {r, "working"} end) |> Enum.into(%{}),
tmState: "init",
tmPrepared: MapSet.new([]),
msgs: MapSet.new([])
})
