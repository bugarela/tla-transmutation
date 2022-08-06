------------------- MODULE TrafficSemaphores -----------------------
EXTENDS Integers, FiniteSets
VARIABLE colors, next_to_open
CONSTANT SEMAPHORES

TurnGreen(s) == /\ \A s2 \in SEMAPHORES : colors[s2] = "red"
                /\colors' = [colors EXCEPT ![s] = "green"]
                /\UNCHANGED << next_to_open >>

TurnYellow(s) == /\colors[s] = "green"
                 /\colors' = [colors EXCEPT ![s] = "yellow"]
                 /\UNCHANGED << next_to_open >>

TurnRed(s) == /\colors[s] = "yellow"
              /\colors' = [colors EXCEPT ![s] = "red"]
              /\UNCHANGED << next_to_open >>

Init == colors = [s \in SEMAPHORES |-> "red"] /\next_to_open = 0

Next == \E s \in SEMAPHORES : TurnGreen(s) \/ TurnYellow(s) \/ TurnRed(s)
------------------------------------------------------------
============================================================
\* Modification History
\* Created Tue May 25 14:59:50 2021 by Gabriela Moreira Mafra
