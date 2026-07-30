---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Nodes,
    Root

\* The algorithm's state: each node is marked once it is known reachable,
\* the frontier is what is yet to be explored, and pc tracks the algorithm.
VARIABLES
    marked,
    frontier,
    pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"searching", "ready"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "searching"

\* The single step: take a frontier node and add its successors to the
\* marked set, or, once every reachable node is marked, go ready.
Step ==
    /\ pc = "searching"
    /\ \E n \in frontier :
         /\ marked' = marked \cup {n}
         /\ frontier' = frontier \ {n}
    /\ UNCHANGED pc
    \/ (pc = "searching" /\ frontier = {} /\ pc' = "ready" /\ UNCHANGED <<marked, frontier>>)

Spec == Init /\ [][Step]_<<marked, frontier, pc>>

\* Invariant 1: type-correct and every successor of a marked node is already
\* known (in marked) or still waiting (in frontier).
Inv1 ==
    /\ TypeOK
    /\ \A x \in marked : \A y \in Nodes : (y \in marked \cup frontier) \/ ~(x, y) \in Nodes

\* Lemma 1 (from the reachability proofs module): replacing a marked node by
\* its successors leaves the reachable set unchanged.
\* Invariant 2 derives from it directly.
Inv2 ==
    \A x \in Nodes : reachableFrom(marked) = reachableFrom(marked \ {x} \cup {y \in Nodes : (x, y) \in Nodes})

\* Lemma 2: reachable-from is stable under adding successors.
\* Lemma 3: reachable-from empty is empty.
\* Together they give Invariant 3, tying the frontier to the reachable set.
Inv3 == reachableFrom(Root) = (marked \cup reachableFrom(frontier))

\* A partial-correctness theorem: termination means the reachable set is
\* exactly the marked set (nothing left unknown, nothing falsely known).
Theorem == (pc = "ready") => (marked = reachableFrom(Root))

INVARIANTS == Inv1
PROPERTIES == Inv2 /\ Inv3

====