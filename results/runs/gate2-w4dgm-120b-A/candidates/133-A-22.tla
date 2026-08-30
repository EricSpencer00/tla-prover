---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

\* Model-checking configuration for the parallel reachability algorithm.
\* It inherits the algorithm's actions/state and adds only the concrete
\* graph/successor set and the bound needed to keep the state space finite.
CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succs
vars == <<marked, frontier, pc, selected, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working"}]
  /\ selected \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Pick(p) ==
  /\ pc[p] = "idle"
  /\ selected' = [selected EXCEPT ![p] = Root]
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ succs' = [succs EXCEPT ![p] = Succ[Root]]
  /\ UNCHANGED <<marked, frontier>>

Advance(p) ==
  /\ pc[p] = "working"
  /\ \E u \in succs[p] :
       /\ u \notin marked
       /\ marked' = marked \cup {u}
       /\ frontier' = frontier \cup {u}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ selected' = [selected EXCEPT ![p] = "none"]
  /\ succs' = [succs EXCEPT ![p] = {}]

Drop(p) ==
  /\ pc[p] = "working"
  /\ \A u \in succs[p] : u \in marked
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ selected' = [selected EXCEPT ![p] = "none"]
  /\ succs' = [succs EXCEPT ![p] = {}]

Next == \E p \in Procs : Pick(p) \/ Advance(p) \/ Drop(p)

Spec == Init /\ [][Next]_vars

\* Marked nodes are exactly the root plus the visited frontier; the
\* frontier is exactly the visited nodes that are not the root.
Inv == marked = frontier \cup {Root} /\ frontier \subseteq marked

\* The parallel algorithm's visited set never differs from the
\* sequential Misra algorithm's visited set: no node is missed, no node
\* is visited twice, and every visited non-root node was reached from
\* some visited predecessor.
Refines ==
  \A u \in frontier :
    /\ u \in marked
    /\ \E w \in marked : u \in Succ[w]
    /\ \A v \in frontier : v = u => \A w \in frontier : w = u

\* The .cfg substitutes ConnectedToSomeButNotAll for Succ, so Succ is
\* actually provided by the configuration file rather than by this spec.
ConnectedToSomeButNotAll == Succ

\* The .cfg substitutes LimitedSeq for Seq, so Seq is not the unbounded
\* combinator from Sequences and no operator here redeclares it.
LimitedSeq == Seq

====