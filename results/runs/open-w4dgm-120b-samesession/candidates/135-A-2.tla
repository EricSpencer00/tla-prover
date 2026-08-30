---- MODULE MCReachable ----
EXTENDS Integers, Sequences

\* The configuration module supplies the reachable-set invariants that the
\* sequential reachability algorithm inherits but does not define.  The
\* Succ relation is a concrete constant, not a schema, so the model is
\* finite and exhaustively checkable -- the bounded sequence override is
\* what makes the existential path quantifier decidable.

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "working", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

\* ReachableSet is defined in terms of paths, so the bounded sequence
\* override below is what keeps this finite.  That definition is the
\* entire reason the invariants are decidable at model-check time.
ReachableSet ==
  { y \in Nodes :
      \E k \in 1..Cardinality(Nodes) :
        \E s \in LimitedSeq(Nodes, k) :
          /\ s[1] = Root
          /\ s[k] = y
          /\ \A i \in 1..(k - 1) : s[i + 1] \in Succ[s[i]] }

Work ==
  /\ pc = "idle"
  /\ frontier # {}
  /\ pc' = "working"
  /\ UNCHANGED <<marked, frontier>>

Expand(n) ==
  /\ pc = "working"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ marked' = marked \cup Succ[n]
  /\ frontier' = frontier' \cup Succ[n]
  /\ pc' = IF frontier = {n} THEN "done" ELSE "working"

Done ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Reset ==
  /\ pc = "done"
  /\ pc' = "idle"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Work
  \/ \E n \in frontier : Expand(n)
  \/ Done
  \/ Reset

Spec == Init /\ [][Next]_vars /\ WF_vars(Done)

\* Safety: type correctness plus the three core reachability invariants
\* from the sequential algorithm (closure under successors, frontier =
\* reachable\marked, reachable = reachable\marked) and partial correctness.
Inv1 == \A a \in Nodes : \A b \in Nodes : (a \in marked /\ b \in Succ[a]) => b \in marked
Inv2 == frontier = (ReachableSet \marked)
Inv3 == ReachableSet = (ReachableSet \marked)
PartialCorrectness == FrontierMarkingAgree == (marked \cap frontier = {})
TypeOKInv == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness

\* Liveness: the algorithm always eventually reaches a completed state.
Termination == <>(pc = "done")

\* The .cfg substitutes ConnectedToSomeButNotAll for Succ, which is
\* exactly the constrained graph shape the model depends on.
ConnectedToSomeButNotAll == Succ

\* The .cfg substitutes LimitedSeq for Seq below; it is still implemented
\* in terms of the full, unbounded Seq from Sequences, but the override
\* makes it a finite package, which is what keeps the model checking
\* decidable.  Do NOT redeclare or redefine Seq itself in this module.
LimitedSeq(S, k) == Seq(S)[1..k]

====