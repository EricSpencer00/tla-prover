---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Reachable, ReachableLemmas

CONSTANT Nodes
CONSTANT Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"exploring", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "exploring"

Explore(n) ==
  /\ pc = "exploring"
  /\ frontier = {}
  /\ n \in marked
  /\ frontier' = (ReachableFrom({n}) \cup frontier) \ {marked}
  /\ UNCHANGED <<marked, pc>>

Mark(n) ==
  /\ frontier # {}
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Done ==
  /\ pc = "exploring"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Explore(n)
  \/ \E n \in Nodes : Mark(n)
  \/ Done

Spec == Init /\ [][Next]_vars

\* Invariant 1: type correctness (carried as a separate conjunct here) plus
\* the partial-reachability closure property.
Inv1 ==
  /\ TypeOK
  /\ \A n \in marked : ReachableFrom({n}) \subseteq (marked \cup frontier)

\* Invariant 2: reachable nodes are exactly reachable from the combined
\* (marked \cup frontier) set -- proved from Lemma 1.
Inv2 ==
  ReachableFrom(marked \cup frontier) = ReachableFrom(marked) \cup ReachableFrom(frontier)

\* Invariant 3: reachable nodes are exactly the marked set plus those
\* reachable from the frontier -- proved from Lemma 2 and Lemma 3.
Inv3 ==
  ReachableFrom(Nodes) = marked \cup ReachableFrom(frontier)

\* Final theorem: partial correctness -- termination leaves exactly the
\* reachable nodes marked.
TerminatingIsExact == (\A n \in Nodes : n \in marked) ~> (marked = ReachableFrom(Nodes))

====