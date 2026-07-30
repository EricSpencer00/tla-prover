---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

\* Model-checking configuration for the sequential Misra reachability algorithm.
\* It adds concrete definitions for the graph and a bounded sequence override.
CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init == /\ marked = {Root}
        /\ frontier = {Root}
        /\ pc = "running"

Expand == /\ pc = "running"
          /\ frontier # {}
          /\ \E n \in frontier :
               /\ marked' = marked \cup Succ[n]
               /\ frontier' = frontier \cup Succ[n]
          /\ pc' = IF marked = Nodes THEN "done" ELSE pc

Stall == /\ pc = "running"
         /\ frontier = {}
         /\ marked = Nodes
         /\ pc' = "done"
         /\ UNCHANGED <<marked, frontier>>

Next == Expand \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Expand) /\ WF_vars(Stall)

TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"running", "done"}

Inv1 == frontier \subseteq marked

Inv2 == marked \subseteq Nodes

Inv3 == \A n \in Nodes : n \in marked => (\E k \in DOMAIN Seq : Seq[k] = n)

PartialCorrectness == \A n \in Nodes : n \in marked => Reachable[n]

Termination == <>(pc = "done")

\* A node is reachable if some finite sequence leads to it from the root.
Reachable(n) ==
  \/ n = Root
  \/ \E s \in Seq :
       /\ s # <<>>
       /\ Head(s) = Root
       /\ Last(s) = n
       /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]]
====