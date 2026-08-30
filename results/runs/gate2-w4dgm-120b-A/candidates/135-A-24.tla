---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* Model checking the Misra reachability algorithm needs a concrete node set
\* and a bound on sequence length (override the standard Seq, which is infinite).
CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"init", "running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "init"

MarkStep(n) ==
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier \ {n}
    /\ pc' = IF marked \cup {n} = Nodes THEN "done" ELSE "running"

UnmarkStep(n) ==
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ pc' = "running"
    /\ UNCHANGED marked

MarkAll(n) == MarkStep(n) \/ UnmarkStep(n)

Next ==
    \/ \E n \in Nodes : MarkAll(n)

Spec == Init /\ [][Next]_vars

\* Every node in the frontier is reachable, so its successors are covered.
Inv1 ==
    \A n \in frontier : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
    marked \cap frontier = {}

Inv3 ==
    marked \cup frontier = Nodes

PartialCorrectness ==
    \A n \in Nodes : (\E k \in 1..Cardinality(Nodes) : \E p \in LimitedSeq(Nodes) :
                        /\ Len(p) = k
                        /\ p[1] = Root
                        /\ \A i \in 1..(k - 1) : p[i + 1] \in Succ[p[i]]
                        /\ p[k] = n)

Termination == <>(pc = "done")

\* Backing out from the original, the .cfg file substitutes ConnectedToSomeButNotAll
\* for Succ, a deterministic 2-successor choice per node, and LimitedSeq for Seq.
ConnectedToSomeButNotAll ==
    Succ
LimitedSeq ==
    Seq

====