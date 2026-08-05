---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

Neighbors(n) == { m \in Nodes : m # n }

VARIABLES marked, frontier, pc
vars == << marked, frontier, pc >>

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
    IF S = {} THEN {}
    ELSE LET x == CHOOSE y \in S : TRUE
         IN { x } \cup ReachableFrom(S \cup Neighbors(x))

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"marking", "done"}

Init ==
    /\ marked = {}
    /\ frontier = { Root }
    /\ pc = "marking"

MarkNode ==
    /\ pc = "marking"
    /\ frontier # {}
    /\ \E n \in frontier :
        /\ marked' = marked \cup { n }
        /\ frontier' = (frontier \cup Neighbors(n)) \ { n }
    /\ UNCHANGED pc

Done ==
    /\ pc = "marking"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED << marked, frontier >>

Finalize ==
    /\ pc = "done"
    /\ marked' = {}
    /\ frontier' = {}
    /\ pc' = "done"

Next == MarkNode \/ Done \/ Finalize

Spec == Init /\ [][Next]_vars

\* Invariant 1: type-correctness plus a forward edge property (successors of a
\* marked node are already marked or still in the frontier).
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Neighbors(n) \subseteq (marked \cup frontier)

\* Invariant 2: the marked set plus nodes reachable from the frontier equals
\* nodes reachable from the union of marked and frontier. This is exactly the
\* property established by Lemma 1 of the reachability proofs module.
Inv2 ==
    marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* Invariant 3: reachable nodes from the root equal the marked set plus nodes
\* reachable from the frontier. The proof uses Lemma 2 (successors are stable
\* under reachable-from) and Lemma 3 (reachable from empty set is empty).
Inv3 ==
    ReachableFrom({ Root }) = marked \cup ReachableFrom(frontier)

TypeOKInvariance == Inv1
ReachabilityDecomposition == Inv2
ReachabilityCompleteness == Inv3

====