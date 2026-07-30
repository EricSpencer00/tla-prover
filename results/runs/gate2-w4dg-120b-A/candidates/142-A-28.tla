---- MODULE ReachableProofs ----
EXTENDS Naturals, ReachableDefs, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "working", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

StartExplore ==
  /\ pc = "idle"
  /\ pc' = "working"
  /\ frontier' = {x \in Nodes : Root \in succ(x)}
  /\ UNCHANGED marked

ExploreStep ==
  /\ pc = "working"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \cup {x \in Nodes : n \in succ(x)} \ {n}
  /\ UNCHANGED pc

Finish ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Reset ==
  /\ pc = "done"
  /\ pc' = "idle"
  /\ marked' = {Root}
  /\ frontier' = {}
  /\ UNCHANGED <<>>

Next == StartExplore \/ ExploreStep \/ Finish \/ Reset

Spec == Init /\ [][Next]_vars

Inv1 ==
  /\ TypeOK
  /\ \A m \in marked : \A o \in Nodes : m \in succ(o) => (o \in marked \/ o \in frontier)

Inv2 ==
  \A M \subseteq Nodes :
    reachableFrom(M \cup frontier) = reachableFrom(M) \cup reachableFrom(frontier)

Inv3 == reachableFrom(Root) = marked \cup reachableFrom(frontier)

PartialCorrectness ==
  /\ pc = "done"
  => marked = reachableFrom(Root)

====