---- MODULE ReachableProofs ----
EXTENDS Reachable
CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"working", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "working"

\* The frontier is exactly the unmarked successors of the currently marked set.
Expand ==
    /\ pc = "working"
    /\ frontier = {}
    /\ frontier' = {y \in Nodes : \E x \in marked : E(x, y) /\ y \notin marked}
    /\ UNCHANGED <<marked, pc>>

Mark(n) ==
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ marked' = marked \cup {n}
    /\ UNCHANGED pc

Done ==
    /\ pc = "working"
    /\ frontier = {}
    /\ \A n \in Nodes : (n \in marked) => \A m \in Nodes : E(n, m) => m \in marked
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Expand
    \/ \E n \in Nodes : Mark(n)
    \/ Done

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Invariant 1: type correctness plus successors of marked nodes are marked or
\* on the frontier -- the reachable-from closure cannot grow past them.
Invariant1 ==
    /\ TypeOK
    /\ \A y \in Nodes : (\E x \in marked : E(x, y)) => y \in marked \/ y \in frontier

\* Invariant 2: the marked set plus nodes reachable from the frontier is exactly
\* the set reachable from the combined marked+frontier. This is the direct
\* consequence of Lemma 1 (reachability from a union of closed sets).
Invariant2 ==
    marked \cup ReachableFrom(Nodes, frontier) = ReachableFrom(Nodes, marked \cup frontier)

\* Invariant 3: the reachable set from the root is the marked set plus nodes
\* reachable from the frontier. Reachable-from stability under adding
\* successors (Lemma 2) and the empty-set case (Lemma 3) are used in its proof.
Invariant3 ==
    ReachableFrom(Nodes, {Root}) = marked \cup ReachableFrom(Nodes, frontier)

\* The partial correctness statement: on termination, marking is complete.
PartialCorrect == pc = "done" => marked = ReachableFrom(Nodes, {Root})
====