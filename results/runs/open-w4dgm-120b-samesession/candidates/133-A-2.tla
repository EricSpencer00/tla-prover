---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

\* A bounded variant of Succ: the graph is fixed to every node having
\* exactly 2 successors, which is what keeps Reachable finite.
ConnectedToSomeButNotAll(n) == Succ[n]

VARIABLES marked, frontier, pc, sel, succs
vars == <<marked, frontier, pc, sel, succs>>

\* A sequence limited to the number of nodes, so the state space stays finite.
LimitedSeq == [n \in 1..Cardinality(Nodes) |-> Nodes]

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in [Procs -> {"idle", "selecting", "visiting"}]
  /\ sel \in [Procs -> Nodes]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> Root]
  /\ succs = [p \in Procs |-> {}]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED <<marked, frontier>>

Visit(p) ==
  /\ pc[p] = "selecting"
  /\ pc' = [pc EXCEPT ![p] = "visiting"]
  /\ succs' = [succs EXCEPT ![p] = ConnectedToSomeButNotAll(sel[p])]
  /\ UNCHANGED <<marked, frontier, sel>>

VisitAny == \E p \in Procs : Visit(p)

Finish(p) ==
  /\ pc[p] = "visiting"
  /\ frontier' = (frontier \ {sel[p]}) \cup succs[p]
  /\ marked' = marked \cup succs[p]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<sel, succs>>

FinishAny == \E p \in Procs : Finish(p)

FinishAnyStep == FinishAny \/ VisitAny

SomeVisiting == \E p \in Procs : pc[p] = "visiting"

Next ==
  \/ FinishAnyStep
  \/ \E p \in Procs, n \in Nodes : Select(p, n)

Spec == Init /\ [][Next]_vars /\ WF_vars(FinishAnyStep) /\ SF_vars(VisitAny)

Inv ==
  /\ TypeOK
  /\ marked \cup frontier = Nodes
  /\ marked \cap frontier = {}
  /\ \A p \in Procs : pc[p] = "selecting" => sel[p] \in frontier

\* Visits and finishes of different processes may interleave arbitrarily
\* -- the refinement only cares that the marking never lags behind the
\* frontier, not which process got there first.
Refines == []<>(~SomeVisiting)
====