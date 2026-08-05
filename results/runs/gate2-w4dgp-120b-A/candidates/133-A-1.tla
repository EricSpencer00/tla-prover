---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* The parallel reachability algorithm's reachability set must stay a superset of
\* whatever the sequential algorithm computed on the same (finite) graph.
RECURSIVE Succs(_)
Succs(n) == Succ[n] \cup (IF n \in DOMAIN Succ THEN Succs(Succ[n]) ELSE {})

VARIABLES marked, frontier, pc, sel, succs

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "exploring", "done"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Select(p) ==
  /\ pc[p] = "idle"
  /\ sel' = [sel EXCEPT ![p] = CHOOSE n \in frontier : \A m \in frontier : n <= m]
  /\ pc' = [pc EXCEPT ![p] = "exploring"]
  /\ UNCHANGED <<marked, frontier, succs>>

Explore(p) ==
  /\ pc[p] = "exploring"
  /\ succs' = [succs EXCEPT ![p] = Succs(sel[p])]
  /\ UNCHANGED <<marked, frontier, pc, sel>>

Mark(p) ==
  /\ pc[p] = "exploring"
  /\ \E n \in succs[p] :
       /\ n \notin marked
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \cup {n}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ succs' = [succs EXCEPT ![p] = {}]

ExploreComplete(p) ==
  /\ pc[p] = "exploring"
  /\ \A n \in sel[p] : n \in marked
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E p \in Procs : Select(p)
  \/ \E p \in Procs : Explore(p)
  \/ \E p \in Procs : Mark(p)
  \/ \E p \in Procs : ExploreComplete(p)

Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succs>>

\* SAFETY INVARIANT: consistent typing with the extended process view.
Inv == TypeOK

\* REFINEMENT PROPERTY: the parallel reachable set stays a superset of the
\* sequential reachable set on the same (finite) graph.
Refines == Root \in marked /\ \A n \in Nodes : (n \in reachable) => (n \in marked)

====