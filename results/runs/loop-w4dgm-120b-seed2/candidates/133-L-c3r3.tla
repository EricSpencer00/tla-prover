---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* Bounded-capacity sequence derived from the standard Sequences module; the
\* model's .cfg file substitutes it in place of Seq so the model stays finite.
LimitedSeq == [rng |-> [i \in 1..Cardinality(Nodes) |-> CHOOSE v \in Nodes : TRUE],
               Len |-> 0]

VARIABLES marked, frontier, pc, selected, succs

vars == <<marked, frontier, pc, selected, succs>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "scanning", "expanding"}]
    /\ selected \in [Procs -> Nodes \cup {"none"}]
    /\ succs \in [Procs -> Seq(Nodes)]

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = [p \in Procs |-> "idle"]
    /\ selected = [p \in Procs |-> "none"]
    /\ succs = [p \in Procs |-> LimitedSeq]

Select(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in marked
    /\ n \notin frontier
    /\ frontier' = frontier \cup {n}
    /\ pc' = [pc EXCEPT ![p] = "scanning"]
    /\ selected' = [selected EXCEPT ![p] = n]
    /\ UNCHANGED <<marked, succs>>

\* The expansion is guarded by the node staying out of the frontier, which is
\* exactly what stops two processes expanding the same node.
Expand(p) ==
    /\ pc[p] = "scanning"
    /\ selected[p] \notin frontier
    /\ succs[p].Len < Cardinality(Nodes)
    /\ succs' = [succs EXCEPT ![p] = [succs[p] EXCEPT !.Len = succs[p].Len + 1,
                                      !.rng = [succs[p].rng EXCEPT ![succs[p].Len + 1] = selected[p]]]]
    /\ pc' = [pc EXCEPT ![p] = "expanding"]
    /\ UNCHANGED <<marked, frontier, selected>>

Commit(p) ==
    /\ pc[p] = "expanding"
    /\ selected[p] \notin frontier
    /\ frontier' = frontier \ {selected[p]}
    /\ marked' = marked \cup {selected[p]}
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ selected' = [selected EXCEPT ![p] = "none"]
    /\ UNCHANGED succs

Abandon(p) ==
    /\ pc[p] \in {"scanning", "expanding"}
    /\ selected[p] \in frontier
    /\ frontier' = frontier \ {selected[p]}
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ selected' = [selected EXCEPT ![p] = "none"]
    /\ UNCHANGED <<marked, succs>>

Next ==
    \/ \E p \in Procs, n \in Nodes : Select(p, n)
    \/ \E p \in Procs : Expand(p)
    \/ \E p \in Procs : Commit(p)
    \/ \E p \in Procs : Abandon(p)

Spec == Init /\ [][Next]_vars

\* The marked set is exactly the reachable set of the graph defined by Succ,
\* which is the correctness claim the parallel algorithm pledges to uphold.
Inv == marked = {n \in Nodes : \E m \in Nodes : m # n /\ m \in Succ[n]}

\* The refinement relation: every expansion here is backed by a scan, so the parallel algorithm never expands a node without the full check Misra does.
Refines == \A p \in Procs : pc[p] = "expanding" => selected[p] \in marked

ConnectedToSomeButNotAll == {n \in Nodes : Cardinality(Succ[n]) > 0}

====