---- MODULE ACTION -------------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
TMRcvPrepared(r) ==
(*************************************************************************)
(* The TM receives a "Prepared" message from resource manager r.  We     *)
(* could add the additional enabling condition r \notin tmPrepared,      *)
(* which disables the action if the TM has already received this         *)
(* message.  But there is no need, because in that case the action has   *)
(* no effect; it leaves the state unchanged.                             *)
(*************************************************************************)
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> r] \in msgs
  /\ tmPrepared' = tmPrepared \cup {r}
  /\ UNCHANGED <<rmState, tmState, msgs>>

================================================================================
