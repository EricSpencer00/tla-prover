---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* A node is reachable iff it appears somewhere in some path from the root.
\* The sequence type here is bounded (Seq) to keep the state space finite.
Reachable(n) ==
  \E s \in Seq : Len(s) > 0 /\ Head(s) = Root /\ s[Len(s)] = n
                   /\ \A i \in 1..(Len(s) - 1) : s[i+1] \in Succ[s[i]]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "running"

Step(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ \E m \in Succ[n] :
       /\ m \notin marked
       /\ marked' = marked \cup {m}
       /\ frontier' = (frontier \cup {m}) \ {n}
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == (\E n \in Nodes : Step(n)) \/ Terminate

Spec == Init /\ [][Next]_vars

\* Type correctness: each variable stays within its intended domain.
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

\* Every node reachable in the graph is present in the algorithm's marked set.
Inv1 == \A n \in Nodes : Reachable(n) => n \in marked

\* Every node in the frontier is reachable, so no reachable node is lost.
Inv2 == \A n \in frontier : Reachable(n)

\* The algorithm's view of reachable nodes equals the graph-theoretic reachability.
Inv3 == marked = {n \in Nodes : Reachable(n)}

PartialCorrectness == \A n \in Nodes : Reachable(n) => n \in marked

Termination == <>(pc = "done")

====