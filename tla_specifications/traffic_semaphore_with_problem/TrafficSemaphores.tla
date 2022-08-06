------------------- MODULE TrafficSemaphores -----------------------
EXTENDS Integers, FiniteSets
VARIABLE colors
CONSTANT SEMAPHORES

TurnGreen(s) == /\ \A s2 \in SEMAPHORES : colors[s2] = "red"
                /\colors' = [colors EXCEPT ![s] = "green"]

TurnYellow(s) == /\colors[s] = "green"
                 /\colors' = [colors EXCEPT ![s] = "yellow"]

TurnRed(s) == /\colors[s] = "yellow"
              /\colors' = [colors EXCEPT ![s] = "red"]

Init == colors = [s \in SEMAPHORES |-> "red"]

Next == \E s \in SEMAPHORES : TurnGreen(s) \/ TurnYellow(s) \/ TurnRed(s)
------------------------------------------------------------
============================================================
\* Modification History
\* Created Tue May 25 14:59:50 2021 by Gabriela Moreira Mafra
