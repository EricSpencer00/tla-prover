---- MODULE ReachableProofs ----
EXTENDS Naturals

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

Init0 == \/ marked = {}
         \/ frontier = {}
         \/ pc = 0

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {0, 1}

Init ==
  /\ Init0
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = 0

Expand ==
  /\ pc = 0
  /\ frontier = {}
  /\ \E n \in Nodes :
       /\ n \in marked
       /\ frontier' = {n}
  /\ pc' = 1
  /\ UNCHANGED marked

Visit ==
  /\ pc = 1
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Done ==
  /\ pc = 1
  /\ frontier = {}
  /\ \A n \in Nodes : n \in marked
  /\ pc' = 0
  /\ UNCHANGED << marked, frontier >>

Next == Expand \/ Visit \/ Done

Spec == Init /\ [][Next]_vars

TypeOKInv == TypeOK

FrontierStable ==
  /\ \A x \in marked : (\E y \in marked \cup frontier : y = x)
  /\ \A x \in frontier : (\E y \in marked \cup frontier : y = x)

FromFrontier ==
  /\ ReachableFrom(Root, marked) \cup ReachableFrom(Root, frontier)
       = ReachableFrom(Root, marked \cup frontier)

FromMarked ==
  /\ ReachableFrom(Root, Root) = marked \cup ReachableFrom(Root, frontier)

Terminating ==
  /\ pc = 0
  /\ frontier = {}
  /\ \A n \in Nodes : n \in marked
  /\ marked = ReachableFrom(Root, Root)

INVARIANTS == TypeOKInv /\ FrontierStable /\ FromFrontier /\ FromMarked
PROPERTIES == Terminating
====