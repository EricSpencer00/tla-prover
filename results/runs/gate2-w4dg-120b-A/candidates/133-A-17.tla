---- MODULE MCParReach ----
EXTENDS Naturals

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES mark, frontier, pc, sel, succset

vars == <<mark, frontier, pc, sel, succset>>

RECURSIVE UnionOf(_, _)
UnionOf(f, S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] \union UnionOf(f, S \ {x})

TypeOK ==
  /\ mark \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in [Procs -> {"idle", "working", "done"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succset \in [Procs -> SUBSET Nodes]

Init ==
  /\ mark = {Root}
  /\ frontier = Succ[Root]
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succset = [p \in Procs |-> {}]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succset' = [succset EXCEPT ![p] = Succ[n]]
  /\ UNCHANGED mark

Mark(p) ==
  /\ pc[p] = "working"
  /\ mark' = mark \union succset[p]
  /\ frontier' = frontier \union succset[p]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<sel, succset>>

Reset(p) ==
  /\ pc[p] = "done"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ succset' = [succset EXCEPT ![p] = {}]
  /\ UNCHANGED <<mark, frontier>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Mark(p)
  \/ \E p \in Procs : Reset(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TRUE

====