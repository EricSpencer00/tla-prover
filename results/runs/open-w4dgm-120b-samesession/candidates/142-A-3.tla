---- MODULE ReachableProofs ----
EXTENDS ReachableAlgorithm, ReachableLemmas

CONSTANTS Nodes, Root

\* The action set is exactly those of the sequential reachability algorithm;
\* ReachableLemmas supplies the graph-theoretic lemmas the TLAPS proofs call.
Init == ReachableAlgorithm.Init
Mark == ReachableAlgorithm.Mark
Explore == ReachableAlgorithm.Explore
Saturate == ReachableAlgorithm.Saturate
Done == ReachableAlgorithm.Done

Next == Mark \/ Explore \/ Saturate \/ Done

Spec == ReachableAlgorithm.Spec

\* Invariant 1: type correctness plus the frontier closure condition, which
\* is the substance of the inductive claim the other two invariants rely on.
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"exploring", "done"}
  /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

\* Lemma 1 turns this closure fact into the marked+frontier reachable-union
\* identity; it is the real work that keeps the reachable set from drifting.
FrontierClosure == TypeOK /\ (marked \cup frontier = ReachableFrom({Root}))

\* Lemma 2 is what lets the reachable set absorb a frontier-successor step
\* without changing shape; Lemma 3 grounds the base case of emptiness.
AttractorStability ==
  FrontierClosure /\ ReachableFromEmpty == {}
  /\ (ReachableFrom({Root}) = marked)

PartialCorrectness == AttractorStability /\ (\A n \in Nodes : pc = "done" => marked = ReachableFrom({n}))

Invariant2 == FrontierClosure
Invariant3 == AttractorStability
TerminationThm == PartialCorrectness

StateInv == Invariant2 /\ Invariant3
StateProps == TypeOK /\ TerminationThm
====