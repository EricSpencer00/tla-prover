---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachable, ReachableAlgs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Step ==
  /\ pc = "running"
  /\ frontier # {}
  /\ LET n == CHOOSE x \in frontier : TRUE IN
       /\ marked' = marked \cup {n}
       /\ frontier' = (frontier \ {n}) \cup (Adj[n] \ marked)
  /\ UNCHANGED pc

Terminate ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Terminate

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}
  /\ (marked # {} => Root \in marked)

ReachableConsistent ==
  \A n \in Nodes : \A m \in Adj[n] : n \in marked => (m \in marked \/ m \in frontier)

FrontierClosure ==
  marked \cup ReachableFrom(frontier, Adj) = ReachableFrom(marked \cup frontier, Adj)

FrontierCollectsReachable ==
  ReachableFrom({Root}, Adj) = marked \cup ReachableFrom(frontier, Adj)

UponTermination ==
  pc = "done" => marked = ReachableFrom({Root}, Adj)

INVARIANTS == TypeOK /\ ReachableConsistent /\ FrontierClosure /\ FrontierCollectsReachable

PROPERTIES == UponTermination

====