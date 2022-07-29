------------------------------- MODULE APAEWD840 -------------------------------
(***************************************************************************)
(* TLA+ specification of an algorithm for distributed termination          *)
(* detection on a ring, due to Dijkstra, published as EWD 840:             *)
(* Derivation of a termination detection algorithm for distributed         *)
(* computations (with W.H.J.Feijen and A.J.M. van Gasteren).               *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Int;
    N

MaxN == 20
CInit3 == N = 3
ConstInit4 == N \in {4}
ConstInit10 == N \in {10}
ConstInitAll20 == N \in 2..50

(*ASSUME NAssumption == N \in Nat \ {0}*)

VARIABLES
    \* @type: Int -> Bool;
    active,
    \* @type: Int -> Str;
    color,
    \* @type: Int;
    tpos,
    \* @type: Str;
    tcolor

Nodes == {i \in 0..MaxN : i < N } \* 0 .. N-1
Color == {"white", "black"}

\* TypeOK ==
\*   /\ active \in [Nodes -> BOOLEAN]    \* status of nodes (active or passive)
\*   /\ color \in [Nodes -> Color]       \* color of nodes
\*   /\ tpos \in Nodes                   \* token position
\*   /\ tcolor \in Color                 \* token color

(***************************************************************************)
(* Initially the token is black. The other variables may take any          *)
(* "type-correct" values.                                                  *)
(***************************************************************************)
Init ==
  /\ active = [n \in Nodes |-> TRUE]
  /\ color = [n \in Nodes |-> "white"]
  /\ tpos = 0
  /\ tcolor = "black"

(***************************************************************************)
(* Node 0 may initiate a probe when it has the token and when either it is *)
(* black or the token is black. It passes a white token to node N-1 and    *)
(* paints itself white.                                                    *)
(***************************************************************************)
InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ active' = active
  /\ color' = [color EXCEPT ![0] = "white"]

(***************************************************************************)
(* A node i different from 0 that possesses the token may pass it to node  *)
(* i-1 under the following circumstances:                                  *)
(*   - node i is inactive or                                               *)
(*   - node i is colored black or                                          *)
(*   - the token is black.                                                 *)
(* Note that the last two conditions will result in an inconclusive round, *)
(* since the token will be black. The token will be stained if node i is   *)
(* black, otherwise its color is unchanged. Node i will be made white.     *)
(***************************************************************************)
PassToken(i) == 
  /\ tpos = i
  /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ active' = active
  /\ color' = [color EXCEPT ![i] = "white"]

(***************************************************************************)
(* An active node i may activate another node j by sending it a message.   *)
(* If j>i (hence activation goes against the direction of the token being  *)
(* passed), then node i becomes black.                                     *)
(***************************************************************************)
SendMsg(i, j) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
  /\ UNCHANGED <<tpos, tcolor>>

(***************************************************************************)
(* Any active node may become inactive at any moment.                      *)
(***************************************************************************)
Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tpos, tcolor>>


(***************************************************************************)
(* next-state relation: disjunction of above actions                       *)
(***************************************************************************)
Next == \/ InitiateProbe
        \/ \E i \in Nodes \ {0} : PassToken(i)
        \/ \E i \in Nodes : \/ \E j \in Nodes \ {i} : SendMsg(i, j)
                            \/ Deactivate(i)

vars == <<active, color, tpos, tcolor>>

-----------------------------------------------------------------------------

(***************************************************************************)
(* Non-properties, useful for validating the specification with TLC.       *)
(***************************************************************************)
TokenAlwaysBlack == tcolor = "black"

Test == TRUE

NeverChangeColor == [][ UNCHANGED color ]_vars

(***************************************************************************)
(* Main safety property: if there is a white token at node 0 then every    *)
(* node is inactive.                                                       *)
(***************************************************************************)
terminationDetected ==
  /\ tpos = 0 /\ tcolor = "white"
  /\ color[0] = "white" /\ ~ active[0]

TerminationDetection ==
  terminationDetected => \A i \in Nodes : ~ active[i]

NotTerminationDetection ==
  terminationDetected => \E i \in Nodes : active[i]
(***************************************************************************)
(* Liveness property: termination is eventually detected.                  *)
(***************************************************************************)
Liveness ==
  (\A i \in Nodes : ~ active[i]) ~> terminationDetected

(***************************************************************************)
(* The following property asserts that when every process always           *)
(* eventually terminates then eventually termination will be detected.     *)
(* It does not hold since processes can wake up each other.                *)
(***************************************************************************)
FalseLiveness ==
  (\A i \in Nodes : []<> ~ active[i]) ~> terminationDetected

full == TRUE

(***************************************************************************)
(* The following property says that eventually all nodes will terminate    *)
(* assuming that from some point onwards no messages are sent. It is       *)
(* not supposed to hold: any node may indefinitely perform local           *)
(* computations. However, this property is verified if the fairness        *)
(* condition WF_vars(Next) is used instead of only WF_vars(System) that    *)
(* requires fairness of the actions controlled by termination detection.   *)
(***************************************************************************)

SpecWFNext == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Dijkstra's inductive invariant                                          *)
(***************************************************************************)
Inv == 
  \/ P0:: \A i \in Nodes : tpos < i => ~ active[i]
  \/ P1:: \E j \in Nodes: (0 <= j /\ j <= tpos) => color[j] = "black"
  \/ P2:: tcolor = "black"

  (*\/ P1:: \E j \in 0 .. tpos : color[j] = "black"*)
  
(* InvAndTypeOK == TypeOK /\ Inv *)

(***************************************************************************)
(* Use the following specification to let TLC check that the predicate     *)
(* TypeOK /\ Inv is inductive for EWD 840: verify that it is an            *)
(* (ordinary) invariant of a specification obtained by replacing the       *)
(* initial condition by that conjunction.                                  *)
(***************************************************************************)
CheckInductiveSpec == Inv /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Wed Mar 20 16:57:55 CET 2019 by igor
\* Last modified Tue Jun 28 18:17:45 CEST 2016 by merz
\* Created Mon Sep 09 11:33:10 CEST 2013 by merz
