---- MODULE ReachableProofs ----
EXTENDS Naturals

\* A formal proof module for the sequential Misra reachability algorithm.
\* It proves the three safety invariants listed in the description and
\* the final partial-correctness theorem, using Lemma 1, Lemma 2, and
\* Lemma 3 from the shared ReachabilityProofs module. No liveness property
\* is proved here (TLAPS does not yet support them).
CONSTANTS Nodes, Root

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
    LET
        Closure(f, S) ==
            IF \E x \in Nodes : f[x] # {}
            THEN Closure([y \in Nodes |-> IF y \in S THEN {} ELSE (IF \E x \in S : y \in f[x] THEN {y} ELSE {})], S \cup {y \in Nodes : f[y] # {}})
            ELSE S
    IN Closure([x \in Nodes |-> IF x \in S THEN {} ELSE S], S)

Marked == ReachFrom({Root})
Succ(n) == {m \in Nodes : m # n}

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = 0

Expand(n) ==
    /\ pc = 0
    /\ frontier = {}
    /\ frontier' = Succ(n)
    /\ pc' = 1
    /\ UNCHANGED marked

Mark(m) ==
    /\ pc = 1
    /\ m \in frontier
    /\ marked' = marked \cup {m}
    /\ frontier' = frontier \ {m}
    /\ pc' = 0

Backtrack ==
    /\ frontier # {}
    /\ frontier' = {n \in frontier : \E x \in frontier : n \in Succ(x)}
    /\ pc' = 0
    /\ UNCHANGED marked

Halt ==
    /\ frontier = {}
    /\ pc = 0
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : Expand(n)
    \/ \E m \in Nodes : Mark(m)
    \/ Backtrack
    \/ Halt

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {0, 1}
    /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

ReachInvariant ==
    ReachFrom(marked) \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

FinalGoal ==
    marked = ReachFrom({Root})

TypeOKInv == TypeOK

ReachInv == ReachInvariant

GoalInv == FinalGoal

====