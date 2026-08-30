---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

ASSUME Root \in Nodes

\* A deterministic 2-successor structure over exactly the nodes in Nodes.
\* The constant Succ is forced to be functional on Nodes: Succ[n] is exactly
\* the two successors the model-checker will consider for any node n.
\* The override below binds Succ to a concrete function satisfying that.
ASSUME Succ \in [Nodes -> SUBSET Nodes]
ASSUME /\ \A n \in Nodes : Cardinality(Succ[n]) = 2
       /\ \A n \in Nodes : \A m \in Nodes : (m \in Succ[n]) => m \in Nodes

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"idle", "working", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

Step ==
    /\ pc = "idle"
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = {}
    /\ pc' = "working"
    /\ UNCHANGED <<>>

Expand(n) ==
    /\ pc = "working"
    /\ n \in frontier
    /\ frontier' = (frontier \ {n}) \cup Succ[n]
    /\ UNCHANGED <<marked, pc>>

Commit ==
    /\ pc = "working"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Reset ==
    /\ pc = "done"
    /\ marked' = {}
    /\ frontier' = {Root}
    /\ pc' = "idle"

Next ==
    \/ Step
    \/ \E n \in Nodes : Expand(n)
    \/ Commit
    \/ Reset

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Commit) /\ WF_vars(Reset)

\* Invariant: every node in the current frontier is reachable from some
\* already-marked node by a non-empty path -- nothing is expanded out of
\* thin air, but the reachable part of the graph can still grow.
Inv1 ==
    \A m \in frontier :
        \E o \in marked :
            \E p \in LimitedSeq(Nodes) :
                /\ Len(p) >= 1
                /\ Head(p) = o
                /\ Last(p) = m
                /\ \A k \in 1..(Len(p) - 1) : p[k + 1] \in Succ[p[k]]

\* The marked set is closed under taking successors, so no reachable node
\* is ever left behind once it has been pulled into the explored set.
Inv2 ==
    \A n \in marked : \A m \in Succ[n] : m \in marked

\* The marked set is exactly the union of the reachability frontiers of
\* every node that has already been pulled into it -- every reachable node
\* is accounted for and nothing more is, modulo the order of discovery.
Inv3 ==
    marked = {m \in Nodes : \E o \in {Root} \cup marked : m \in Succ[o]}

\* Partial correctness: every node that is reachable from the root by a
\* non-empty path is in the marked set, so the algorithm never drops out.
PartialCorrectness ==
    \A m \in Nodes :
        (\E p \in LimitedSeq(Nodes) : Len(p) >= 1 /\ Head(p) = Root /\ Last(p) = m /\ \A k \in 1..(Len(p) - 1) : p[k + 1] \in Succ[p[k]])
            => m \in marked

Termination == <>(pc = "done")

====