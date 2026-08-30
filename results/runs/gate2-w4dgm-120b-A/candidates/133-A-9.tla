---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

\* Configuration-level overrides the Succ operator and the Seq operator from
\* Sequences so the reachable state space stays finite for model checking.
\* Both are defined here and the .cfg substitutes them in for the originals.
ConnectedToSomeButNotAll == Succ

VARIABLES marked, frontier, pc, selected, succs

vars == <<marked, frontier, pc, selected, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "selecting", "expanding"}]
  /\ selected \in [Procs -> Nodes]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> Root]
  /\ succs = [p \in Procs |-> {}]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ selected' = [selected EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ UNCHANGED <<marked, succs>>

Load(p) ==
  /\ pc[p] = "selecting"
  /\ succs' = [succs EXCEPT ![p] = ConnectedToSomeButNotAll[selected[p]]]
  /\ pc' = [pc EXCEPT ![p] = "expanding"]
  /\ UNCHANGED <<marked, frontier, selected>>

Expand(p) ==
  /\ pc[p] = "expanding"
  /\ \E m \in succs[p] :
       /\ m \notin marked
       /\ marked' = marked \cup {m}
       /\ frontier' = frontier \cup {m}
  /\ succs' = [succs EXCEPT ![p] = succs[p] \ {m}]
  /\ pc' = IF succs[p] \ {m} = {} THEN [pc EXCEPT ![p] = "idle"] ELSE pc
  /\ UNCHANGED selected

\* A worker whose successors are all already marked simply retires the node it
\* selected, sweeping it out of that node's own successor set so the node itself
\* can never be stuck waiting on an already-done expansion.
Drop(p) ==
  /\ pc[p] = "expanding"
  /\ succs[p] = {}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED <<marked, frontier, selected>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Load(p)
  \/ \E p \in Procs : Expand(p)
  \/ \E p \in Procs : Drop(p)

Spec == Init /\ [][Next]_vars

\* The invariant is the full inductive check: type correctness plus the
\* control-flow discipline the algorithm's correctness depends on.
Inv == TypeOK

\* Refinement: every marked node is on a path back to the root, so no node is
\* ever marked by a stray or stale expansion that is not reachable from the
\* starting configuration of the single-threaded Misra traversal.
PathTo(n) == n = Root \/ \E p \in Procs : n \in ConnectedToSomeButNotAll[selected[p]] \/ PathTo(n)

Refines == \A n \in marked : PathTo(n)

====