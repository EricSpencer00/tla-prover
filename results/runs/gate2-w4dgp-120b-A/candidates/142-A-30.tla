---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets
CONSTANTS Nodes, Root
ASSUME Root \in Nodes

RECURSIVE Reachable(_)
Reachable(g) ==
  LET expand(S) == S \cup {w \in Nodes : \E v \in S : <<v, w>> \in g}
  IN LET iter(k) == IF k = 0 THEN {} ELSE expand(iter(k-1))
     IN iter(NatCardinality(Nodes))

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "explore", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

Explore ==
  /\ pc = "start"
  /\ marked' = marked \cup frontier
  /\ frontier' = {w \in Nodes : \E v \in frontier : <<v, w>> \in Nodes \X Nodes} \ marked
  /\ pc' = "explore"

Done ==
  /\ pc = "explore"
  /\ frontier = {}
  /\ pc' = "done"
  /\ marked' = marked
  /\ frontier' = frontier

SPEC == Init /\ [][Explore \/ Done]_vars

LabeledInvariant ==
  /\ TypeOK
  /\ \A v \in marked, w \in Nodes : <<v, w>> \in Nodes \X Nodes => w \in marked \cup frontier

Invariant2 == marked \cup Reachable({w \in Nodes : \E v \in frontier : <<v, w>> \in Nodes \X Nodes}) = Reachable(marked \cup frontier)

Invariant3 == Reachable(Root) = marked \cup Reachable({w \in Nodes : \E v \in frontier : <<v, w>> \in Nodes \X Nodes})

Invariant2DerivedFromLemma1 == Lemma1 /\ Invariant2
Invariant3DerivedFromLemma2Lemma3 == Lemma2 /\ Lemma3 /\ Invariant3

INVARIANTS == LabeledInvariant /\ Invariant2DerivedFromLemma1 /\ Invariant3DerivedFromLemma2Lemma3

PartialCorrectness == pc = "done" => marked = Reachable(Root)
PROPERTIES == PartialCorrectness
====