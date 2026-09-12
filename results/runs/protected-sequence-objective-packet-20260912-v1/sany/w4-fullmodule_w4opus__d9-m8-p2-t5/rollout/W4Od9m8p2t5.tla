---- MODULE W4Od9m8p2t5 ----
EXTENDS Naturals, FiniteSets

CONSTANTS R1, Region, c1, c2, Nom1, Nom2, g1, g2, Agent, NoAgent

VARIABLES reserve, circuitLoads

vars == <<circuitLoads, reserve>>

Init == /\ reserve = 0
       /\ circuitLoads = [c1 |-> Nom1, c2 |-> Nom2]

Next == \/ \E c \in R1 : circuitLoads' = circuitLoads \cup {[c |-> (circuitLoads[c] - 1)]}
       \/ \E c \in R1 : circuitLoads' = circuitLoads \cup {[c |-> (circuitLoads[c] + 1)]}
       \/ \E c \in R1, a \in {Agent, NoAgent} : circuitLoads' = circuitLoads \cup {[c |-> (circuitLoads[c] - 1)]}, reserve' = reserve + Nom1}
       \/ \E c \in R1, a \in {Agent, NoAgent} : circuitLoads' = circuitLoads \cup {[c |-> (circuitLoads[c] + 1)]}, reserve' = reserve - Nom1}
       \/ reserve' = reserve + Nom1
       \/ reserve' = reserve - Nom1
       /\ reserve \in 0..(Nom1 + Nom2)
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
       /\ reserve \in 0..(Nom1 + Nom2) /\ circuitLoads' \in [c1 |-> 0..Nom1, c2 |-> 0..Nom2]
