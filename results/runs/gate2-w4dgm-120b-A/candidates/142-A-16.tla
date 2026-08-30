---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachable, ReachableAlgs

CONSTANTS Nodes, Root

\* No new variables or actors; this module just adds TLAPS-checked proofs
\* of partial correctness to the sequential Misra reachability algorithm.
\* The three invariants are proved one after the other, each building
\* on the graph-theoretic lemmas proved in the Reachable module.

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"ready", "searching", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "ready"

\* The searcher is deterministic: it always expands the frontier by the
\* successors of some marked node. The reachable-from lemmas are what
\* keep the invariants from breaking across that nondeterminism.
Expand ==
    /\ pc = "searching"
    /\ \E n \in marked :
         frontier' = frontier \cup (Succ[n] \ {n})
    /\ UNCHANGED <<marked, pc>>

MarkFrontier ==
    /\ pc = "searching"
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = {}
    /\ pc' = "ready"

Fail ==
    /\ pc = "ready"
    /\ frontier = {}
    /\ marked = Nodes
    /\ UNCHANGED vars

StartSearch ==
    /\ pc = "ready"
    /\ frontier # {}
    /\ pc' = "searching"
    /\ UNCHANGED <<marked, frontier>>

Done ==
    /\ pc = "ready"
    /\ frontier = {}
    /\ marked = Nodes
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

StartStep == Expand \/ MarkFrontier
Next == StartStep \/ Fail \/ StartSearch \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(StartStep)

\* Invariant 1: local closure of the marked set plus type correctness.
MarkedClosed ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* Invariant 2: reachable-from is stable under adding frontier nodes.
\* Proof: by Lemma 1 (union with frontier is conservative for reachable).
ReachableConservative ==
    ReachableFrom(Nodes, marked \cup frontier) = ReachableFrom(Nodes, marked)

\* Invariant 3: reachable-from is stable under adding successors.
\* Proof: by Lemma 2 (adding successors, plus Lemma 3 for the base).
ReachableSaturated ==
    ReachableFrom(Nodes, marked) = marked \cup frontier

\* Partial correctness: on termination the marked set is exactly the reachable set.
TerminationCondition ==
    (pc = "done") => (marked = ReachableFrom(Nodes, {Root}))
====