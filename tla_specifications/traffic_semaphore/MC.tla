------------------- MODULE MC -----------------------
EXTENDS TrafficSemaphores, TLC

no_collision == Cardinality({s \in SEMAPHORES : colors[s] = "green"}) <= 1

never_stuck == WF_<<colors>>(Next) => \A s \in SEMAPHORES :  <>(colors[s] = "green")

property ==  WF_<<colors>>(Next) => \A s \in SEMAPHORES : (colors[s] = "yellow" ~> colors[s] = "red")

full == TRUE

------------------------------------------------------------
============================================================
\* Modification History
\* Created Tue May 25 15:11:17 2021 by Gabriela Moreira Mafra
