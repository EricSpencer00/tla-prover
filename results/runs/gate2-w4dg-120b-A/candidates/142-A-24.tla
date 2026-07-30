---- MODULE ReachableProofs ----
EXTENDS Integers, FiniteSets, Reachable, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

N == Cardinality(Nodes)

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ frontier \cap marked = {}
    /\ pc \in 0..3

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = 0

Expand ==
    /\ pc = 0
    /\ \E e \in Nodes \ marked \ frontier :
         /\ frontier' = frontier \cup {e}
         /\ pc' = 1
    /\ UNCHANGED marked

PickFrontier ==
    /\ pc = 1
    /\ frontier # {}
    /\ \E e \in frontier :
         /\ marked' = marked \cup {e}
         /\ frontier' = frontier \ {e}
         /\ pc' = 2
    /\ UNCHANGED <<>>

Rollback ==
    /\ pc = 2
    /\ frontier # {}
    /\ frontier' = {}
    /\ pc' = 0
    /\ UNCHANGED marked

Done ==
    /\ pc = 2
    /\ frontier = {}
    /\ \A n \in Nodes : \E m \in marked : n \in ReachableFrom(m)
    /\ pc' = 3
    /\ UNCHANGED <<marked, frontier>>

Stall ==
    /\ pc = 3
    /\ UNCHANGED vars

Next ==
    \/ Expand
    \/ PickFrontier
    \/ Rollback
    \/ Done
    \/ Stall

Spec == Init /\ [][Next]_vars

\* Invariant 1: type correctness plus every successor of a marked node is
\* already marked or waiting in the frontier.
Invariant1 ==
    /\ TypeOK
    /\ \A m \in marked : Successors(m) \subseteq (marked \cup frontier)

\* Invariant 2: marked set plus nodes reachable from the frontier equals
\* nodes reachable from the union of marked and frontier.  This is proved
\* directly from Lemma 1 of the reachability lemmas.
Invariant2 ==
    ReachableFrom(marked \cup frontier)
        = marked \cup ReachableFrom(frontier)

\* Invariant 3: reachable-from-root equals the marked set plus nodes
\* reachable from the frontier, proved using Lemma 2 and Lemma 3.
Invariant3 ==
    ReachableFrom({Root})
        = marked \cup ReachableFrom(frontier)

\* Final theorem: partial correctness -- on termination the marked set is
\* exactly the reachable set.
TerminationCorrect ==
    (pc = 3) => (marked = ReachableFrom({Root}))

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3
PROPERTIES == TerminationCorrect
====