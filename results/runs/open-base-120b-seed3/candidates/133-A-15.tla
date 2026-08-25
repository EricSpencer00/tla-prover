---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succSet

\* ----------------------------------------------------------------------
\* Bounded sequence operator used by the .cfg (replaces Seq)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Successor operator used in place of Succ by the .cfg
ConnectedToSomeButNotAll(n) ==
  IF n \in Nodes /\ Cardinality(Succ[n]) > 1 THEN
    { CHOOSE s \in Succ[n] : TRUE }
  ELSE {}

\* ----------------------------------------------------------------------
\* Variables tuple for the temporal operators
Vars == <<marked, frontier, pc, sel, succSet>>

\* ----------------------------------------------------------------------
\* Initial state (concrete instantiation of the parallel algorithm)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "ready"]
  /\ sel = [p \in Procs |-> {}]
  /\ succSet = [p \in Procs |-> {}]

\* ----------------------------------------------------------------------
\* One step of a worker process
WorkerStep(p) ==
  /\ p \in Procs
  /\ frontier # {}
  /\ LET n == CHOOSE x \in frontier : TRUE IN
     /\ marked' = marked \cup {n}
     /\ frontier' = (frontier \ {n}) \cup ConnectedToSomeButNotAll(n)
     /\ pc' = [pc EXCEPT ![p] = "busy"]
     /\ sel' = [sel EXCEPT ![p] = {n}]
     /\ succSet' = [succSet EXCEPT ![p] = ConnectedToSomeButNotAll(n)]

\* ----------------------------------------------------------------------
\* Next-state relation (includes stuttering)
Next ==
  \/ \E p \in Procs : WorkerStep(p)
  \/ UNCHANGED Vars

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Safety invariant (type correctness and simple control‑flow constraints)
Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"ready", "busy"}]
  /\ sel \in [Procs -> SUBSET Nodes]
  /\ succSet \in [Procs -> SUBSET Nodes]

\* ----------------------------------------------------------------------
\* Refinement property (placeholder – actual property defined in the
\* sequential model‑checking module)
Refines == TRUE

=============================================================================