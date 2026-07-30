---- MODULE ReachableProofs ----
EXTENDS Reachability, ReachableAlgorithm

CONSTANTS Nodes, Root

ASSUME /\ Nodes = {}
       /\ Root \in Nodes
       /\ Cardinality(Nodes) > 1

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"searching", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "searching"

Step ==
  /\ pc = "searching"
  /\ \E s \in Nodes :
       /\ s \in marked
       /\ \E t \in Nodes :
            /\ t \notin marked
            /\ t \notin frontier
            /\ frontier' = frontier \cup {t}
  /\ marked' = marked \cup frontier
  /\ frontier' = frontier \ marked
  /\ pc' = pc

Terminate ==
  /\ pc = "searching"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Terminate

Spec == Init /\ [][Next]_vars

Invariant1 ==
  /\ TypeOK
  /\ \A e \in marked : \A d \in Nodes : (e, d) \in Edge => (d \in marked \/ d \in frontier)

Invariant2 ==
  marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 ==
  ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

Completed ==
  /\ pc = "done"
  /\ marked = ReachableFrom(Root)

====