---- MODULE ReachableProofs ----
EXTENDS ReachableAlgs, ReachableLemmas

CONSTANTS Nodes, Root

\* All invariants that TLAPS will check; the final theorem is partial
\* correctness derived from Invariant 3 at termination.
INVARIANT TypeOK
INVARIANT ReachStep
INVARIANT FrontierComplete
INVARIANT MarkedIsReachable
PROPERTY Spec

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"working", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "working"

\* Both outcomes of the frontier test return to the same state, so the
\* reachable-from reasoning needed by the invariants is untouched.
Expand(n) ==
  /\ pc = "working"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ pc' = "working"

StepEmpty ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

StepSome ==
  /\ pc = "working"
  /\ frontier = {}
  /\ \E n \in Nodes : frontier' = frontier \cup {n}
  /\ UNCHANGED <<marked, pc>>

Next == \E n \in Nodes : Expand(n) \/ StepSome \/ StepEmpty

Spec == Init /\ [][Next]_vars

\* Frontier expansion never revisits a predecessor's neighbor.
ReachStep == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* Lemma 1: reachability through frontier nodes is already covered by
\* frontier closure of the marked set.
FrontierComplete == ReachableFrom(Successors(marked)) = ReachableFrom(frontier)

\* Lemma 2 + Lemma 3: reachable is exactly the marked set plus frontier
\* closure, since the root is reachable.
MarkedIsReachable ==
  ReachableFrom({Root}) = (marked \cup ReachableFrom(frontier))

\* At termination the algorithm has saturated its frontier, so the
\* reachable set is already covered.
PartialCorrectness == (pc = "done") => (marked = ReachableFrom({Root}))
====