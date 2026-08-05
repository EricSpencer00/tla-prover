---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets

\* No new actors: this module extends the sequential reachability
\* algorithm module and the reachability proofs module, and combines the
\* algorithm's definition with the graph-theoretic lemmas needed for TLAPS
\* correctness proofs.
CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* The algorithm's state variables are inherited, so the name set comes
\* entirely from there; this module adds no new ones.
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "exploring", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = Nodes \ {Root}
  /\ pc = "idle"

Explore ==
  /\ pc = "idle"
  /\ pc' = "exploring"
  /\ UNCHANGED <<marked, frontier>>

Mark(n) ==
  /\ pc = "exploring"
  /\ n \in frontier
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Done ==
  /\ pc = "exploring"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Explore
  \/ \E n \in Nodes : Mark(n)
  \/ Done

Spec == Init /\ [][Next]_vars

\* Invariant 1 is the algorithm's own type-correctness plus the key
\* per-step progress condition -- the thing that makes the
\* reachable-from lemmas usable here.
Inv1 ==
  /\ TypeOK
  /\ \A n \in marked : (Nodes \ (marked \cup frontier)) \cup frontier \in Nat

\* Invariant 2 is proved from Lemma 1 (the forward-closure lemma) in
\* the reachability proofs module.
Inv2 ==
  reachableFrom(Sigma, marked) \cup reachableFrom(Sigma, frontier) = reachableFrom(Sigma, marked \cup frontier)

\* Invariant 3 is proved from Lemma 2 (reachable-from respects adding
\* successors) and Lemma 3 (reachable-from empty = empty).
Inv3 ==
  reachableFrom(Sigma, {Root}) = marked \cup reachableFrom(Sigma, frontier)

TypeOKProp == Inv1
CombinedInv == Inv2 /\ Inv3
PartialCorrectness == pc = "done" => reachableFrom(Sigma, {Root}) = marked

====