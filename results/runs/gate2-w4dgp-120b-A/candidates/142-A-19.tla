---- MODULE ReachableProofs ----
EXTENDS Integers, Reachability

ASSUME ASSUME_RECURSIVE_DEFINITIONS

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == << marked, frontier, pc >>

Adj == [x \in Nodes |-> {y \in Nodes : x < y /\ x \in frontier /\ y \notin frontier /\ y \notin marked}]

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

Explore ==
  /\ frontier = {}
  /\ frontier' = {z \in Nodes : Root < z}
  /\ pc' = "exploring"
  /\ UNCHANGED marked

Grow(x) ==
  /\ frontier # {}
  /\ x \in frontier
  /\ marked' = marked \cup {x}
  /\ frontier' = frontier \cup Adj[x]
  /\ pc' = "exploring"

Finish ==
  /\ frontier = {}
  /\ pc # "done"
  /\ pc' = "done"
  /\ UNCHANGED << marked, frontier >>

InitStep == Init
ExploreStep == Explore
GrowStep == \E x \in Nodes : Grow(x)
FinishStep == Finish

Next == InitStep \/ ExploreStep \/ GrowStep \/ FinishStep

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "exploring", "done"}
  /\ \A x \in marked : \A y \in Adj[x] : y \in marked \/ frontier

Inv1 ==
  /\ TypeOK
  /\ \A x \in marked : \A y \in Adj[x] : y \in marked \/ frontier

Inv2 ==
  \A x \in marked : reachableFrom(x) \subseteq marked \cup reachableFrom(frontier)

Inv3 ==
  reachableFrom(Root) = marked \cup reachableFrom(frontier)

Theorem ==
  (pc = "done") => (marked = reachableFrom(Root))

====