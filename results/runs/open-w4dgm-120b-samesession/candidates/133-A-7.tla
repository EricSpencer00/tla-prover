---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* Succ is the graph's successor relation; ConnectedToSomeButNotAll is a
\* bounded version of it that the model checker substitutes in.
ConnectedToSomeButNotAll == Succ

VARIABLES marked, frontier, pc, selected, succs

vars == <<marked, frontier, pc, selected, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working", "done"}]
  /\ selected \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

\* Inductive invariant from the parallel algorithm: a worker only ever holds
\* a node it has actually moved from the frontier into the marked set.
Refines ==
  /\ TypeOK
  /\ marked \cup frontier = Nodes
  /\ marked \cap frontier = {}
  /\ \A p \in Procs : pc[p] = "working" => selected[p] \in marked

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Choose(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ marked' = marked \cup {n}
  /\ selected' = [selected EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ succs' = [succs EXCEPT ![p] = {}]

Explore(p) ==
  /\ pc[p] = "working"
  /\ LET nbrs == ConnectedToSomeButNotAll[selected[p]]
         newFrontier == nbrs \ marked
     IN /\ frontier' = frontier \cup newFrontier
        /\ succs' = [succs EXCEPT ![p] = newFrontier]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ selected' = [selected EXCEPT ![p] = "none"]

Reset(p) ==
  /\ pc[p] = "done"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED <<marked, frontier, selected>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Choose(p, n)
  \/ \E p \in Procs : Explore(p)
  \/ \E p \in Procs : Reset(p)

Spec == Init /\ [][Next]_vars

\* The bounded sequence operator the .cfg substitutes in for Seq.
LimitedSeq == FiniteSequences.Seq

====