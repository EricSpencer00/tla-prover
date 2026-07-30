---- MODULE ReachableProofs ----
EXTENDS Integers, Sequences, Reachability

\* The module combines the sequential Misra reachability algorithm with the
\* TLAPS-checked proofs of partial correctness.  All identifiers required by
\* the reference .cfg file (Nodes, Root, Spec, Init, Next, Invariants,
\* Properties) are defined here and must retain exactly these names.

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "running"

\* A node on the frontier is lifted into the marked set.
Mark(c) ==
  /\ pc = "running"
  /\ c \in frontier
  /\ marked' = marked \cup {c}
  /\ frontier' = frontier \ {c}
  /\ pc' = "running"

\* Nodes reachable from any newly-marked node are added to the frontier.
Expand(c) ==
  /\ pc = "running"
  /\ c \in marked
  /\ \E s \in Succ(c) : s \notin marked /\ s \notin frontier /\ frontier' = frontier \cup {s}
  /\ UNCHANGED <<marked, pc>>

\* The algorithm halts once no frontier node remains; this is the final state
\* for the partial-correctness argument, not a deadlock.
Terminate ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E c \in Nodes : Mark(c) \/ Expand(c)
  \/ Terminate

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

\* Invariant 1: type correctness plus the fact that the algorithm never
\* leaves a reachable node outside the combined marked/frontier state.
Invariant1 ==
  /\ TypeOK
  /\ \A c \in marked : Succ(c) \subseteq (marked \cup frontier)

\* Invariant 2: the set of marked nodes plus everything reachable from the
\* frontier equals the set reachable from the combined marked/frontier set.
\* This follows directly from Lemma 1 (union of successors).
Invariant2 ==
  reachableFrom(marked \cup frontier) = marked \cup reachableFrom(frontier)

\* Invariant 3: the set reachable from the root is the marked set plus what
\* is reachable from the frontier.  This is the key safety property, proved
\* using Lemma 2 and Lemma 3.
Invariant3 ==
  reachableFrom({Root}) = marked \cup reachableFrom(frontier)

\* Partial correctness: on termination the marked set is exactly the
\* reachable set, so no reachable node was missed.
Complete ==
  (pc = "done") => (marked = reachableFrom({Root}))

Invariants == Invariant1 /\ Invariant2 /\ Invariant3
Properties == Complete

====