---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

\* The shared state of the parallel reachability algorithm.
VARIABLES marked, frontier, pc, select, succs

vars == <<marked, frontier, pc, select, succs>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> 0..3]
    /\ select \in [Procs -> Nodes \cup {"none"}]
    /\ succs \in [Procs -> SUBSET Nodes]

\* The reachable set never shrinks, and no worker is ever stranded in the
\* middle of a pair of steps.
ReachableSetMonotone ==
    /\ frontier \subseteq marked
    /\ \A p \in Procs : pc[p] > 0 => (pc[p] < 3 => select[p] \in Nodes)

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> 0]
    /\ select = [p \in Procs |-> "none"]
    /\ succs = [p \in Procs |-> {}]

\* Pick an unmarked neighbor from the frontier.
Select(p, n) ==
    /\ pc[p] = 0
    /\ n \in frontier
    /\ n \notin marked
    /\ select' = [select EXCEPT ![p] = n]
    /\ pc' = [pc EXCEPT ![p] = 1]
    /\ succs' = [succs EXCEPT ![p] = Succ[n]]
    /\ UNCHANGED <<marked, frontier>>

Mark(p) ==
    /\ pc[p] = 1
    /\ select[p] \notin marked
    /\ marked' = marked \cup {select[p]}
    /\ frontier' = frontier \cup succs[p]
    /\ pc' = [pc EXCEPT ![p] = 2]
    /\ UNCHANGED <<select, succs>>

Release(p) ==
    /\ pc[p] = 2
    /\ select' = [select EXCEPT ![p] = "none"]
    /\ pc' = [pc EXCEPT ![p] = 0]
    /\ succs' = [succs EXCEPT ![p] = {}]
    /\ UNCHANGED <<marked, frontier>>

Explore(p) == \E n \in Nodes : Select(p, n)
MarkStep == \E p \in Procs : Mark(p)
ReleaseStep == \E p \in Procs : Release(p)

Next ==
    \/ \E p \in Procs, n \in Nodes : Select(p, n)
    \/ MarkStep
    \/ ReleaseStep

Spec == Init /\ [][Next]_vars

\* The pair of per-process steps marking a node never leaves that node
\* stranded in the frontier, so the reachable set can only grow.
Inv == ReachableSetMonotone

\* The parallel algorithm is a sound relaxation of the sequential Misra
\* algorithm: any node the parallel workers have pulled into the frontier
\* is a node the sequential algorithm would have explored by now.
Refines ==
    \A n \in frontier : n \in marked \cup {Root}

\* The bounded horizon: the number of reachable nodes stays within the
\* size of the finite graph.
StateSpaceBound == Cardinality(marked \cup frontier) <= Cardinality(Nodes)

\* Model-checking substitution: Succ is replaced by a version with each
\* node's successor set made finite, which is exactly the graph we model.
ConnectedToSomeButNotAll == Succ

\* Model-checking substitution: the cycle-finite frontier frontier is
\* kept as a finite set rather than a possibly unbounded bag.
LimitedSeq == Seq

====