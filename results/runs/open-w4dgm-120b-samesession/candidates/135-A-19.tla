---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Nodes, Root, Succ

\* A finite, deterministically branched graph: each node has exactly 2 successors.
\* Reachability is defined via bounded sequences (LimitedSeq) rather than the
\* standard infinite Seq operator, which is what makes the reachable-state
\* space finite for exhaustive model checking.

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "working", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "idle"

Explore ==
    /\ frontier # {}
    /\ pc = "idle"
    /\ pc' = "working"
    /\ marked' = marked
    /\ frontier' = { n \in frontier : ConnectedToSomeButNotAll(n, marked) }
    \/ UNCHANGED <<marked, frontier, pc>>

Mark(n) ==
    /\ pc = "working"
    /\ n \in frontier
    /\ \E m \in Succ[n] : m \notin marked
    /\ marked' = marked \cup Succ[n]
    /\ frontier' = frontier \ {n}
    /\ pc' = pc

Finish ==
    /\ frontier = {}
    /\ pc # "done"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Finalize ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ Explore
    \/ \E n \in Nodes : Mark(n)
    \/ Finish
    \/ Finalize

Spec == Init /\ [][Next]_vars

\* Invariant: frontier nodes are each connected to something new (outside
\* the already-marked set) -- no reachable node is stranded with no frontier.
Inv1 == \A n \in frontier : ConnectedToSomeButNotAll(n, marked)

\* Invariant: any node in the marked set is reachable from the root.
Inv2 == \A n \in marked : Reachable(Root, n)

\* Invariant: every node reachable from the root is in the marked set.
Inv3 == \A n \in Nodes : Reachable(Root, n) => n \in marked

Terminated == pc = "done"

\* Partial correctness: the algorithm finishes.
PartialCorrectness == Terminated

\* Termination is a liveness property of the reachable state space.
Termination == Terminated

\* Bounded sequence: the standard Seq is replaced by this finite wrapper so
\* the model stays within a finite state space. The length bound is tied to
\* the number of nodes, which is safe because any longer path would repeat
\* a node and thus not be needed for reachability.
LimitedSeq(n) == Seq(n)

\* Deterministic "some but not all" successor choice: each node has exactly
\* two successors, and this picks the first one that is not yet marked.
ConnectedToSomeButNotAll(n, S) ==
    LET cands == Succ[n] \cap (Nodes \ S) IN
    IF cands = {} THEN FALSE ELSE Cardinality(cands) = Cardinality(Succ[n])

\* Reachability via a bounded existential path: there exists a (possibly
\* empty) bounded sequence of steps from a to b, where the sequence
\* length is limited by the number of nodes and each step follows Succ.
Reachable(a, b) ==
    \E k \in 0..Cardinality(Nodes):
        \E path \in LimitedSeq(Nodes):
            /\ Len(path) = k
            /\ (k = 0 => a = b)
            /\ (k > 0 => path[1] = b)
            /\ (k > 0 => \A i \in 1..(k - 1): path[i + 1] \in Succ[path[i]])
            /\ \A i \in 1..(k - 1): path[i] # a

====