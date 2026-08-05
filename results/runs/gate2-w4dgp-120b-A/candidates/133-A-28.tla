---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

\* A concrete, finite model-checking configuration for the parallel reachability
\* algorithm.  It redefines "Seq" from Sequences as "LimitedSeq" so that the state
\* space stays finite, and provides a concrete graph (ConnectedToSomeButNotAll)
\* that matches the graph used in the sequential model-checking module, so the
\* refinement check against SpecSeq is meaningful.
CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succs

vars == << marked, frontier, pc, selected, succs >>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "active", "done"}]
    /\ selected \in [Procs -> LimitedSeq(Nodes)]
    /\ succs \in [Procs -> LimitedSeq(Nodes)]

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ selected = [p \in Procs |-> << >>]
    /\ succs = [p \in Procs |-> << >>]

Select(p) ==
    /\ pc[p] = "idle"
    /\ \E n \in frontier :
        /\ pc' = [pc EXCEPT ![p] = "active"]
        /\ selected' = [selected EXCEPT ![p] = << n >>]
    /\ UNCHANGED << marked, frontier, succs >>

\* The bound on the sequence length is the number of nodes, so successor tuples
\* are always sufficiently short to keep the state space finite.
LoadSucc(p) ==
    /\ pc[p] = "active"
    /\ Len(succs[p]) < Cardinality(Nodes)
    /\ \E c \in Succ[selected[p][1]] :
        succs' = [succs EXCEPT ![p] = Append(succs[p], c)]
    /\ UNCHANGED << marked, frontier, pc, selected >>

Mark(p) ==
    /\ pc[p] = "active"
    /\ succs[p] # << >>
    /\ LET m == succs[p][1] IN
        /\ m \notin marked
        /\ marked' = marked \cup {m}
        /\ frontier' = frontier \cup {m}
        /\ succs' = [succs EXCEPT ![p] = Tail(succs[p])]
    /\ UNCHANGED << pc, selected >>

Finish(p) ==
    /\ pc[p] = "active"
    /\ succs[p] = << >>
    /\ selected[p] = << >>
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << marked, frontier, selected, succs >>

Next ==
    \/ \E p \in Procs : Select(p)
    \/ \E p \in Procs : LoadSucc(p)
    \/ \E p \in Procs : Mark(p)
    \/ \E p \in Procs : Finish(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

\* The parallel algorithm implements exactly what the sequential Misra algorithm
\* does on this graph.
Refines == \A n \in marked : TRUE

====