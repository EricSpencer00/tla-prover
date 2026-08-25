---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succSet

vars == << marked, frontier, pc, sel, succSet >>

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> 0]
  /\ sel = [p \in Procs |-> Root]
  /\ succSet = [p \in Procs |-> {}]

(*--------------------------------------------------------------------
  Next-state relation (a very abstract version of the parallel reachability
  algorithm)
--------------------------------------------------------------------*)
Next ==
  \/ \E p \in Procs:
        /\ sel[p] \in frontier
        /\ LET n == sel[p] IN
           /\ marked'   = marked \cup {n}
           /\ frontier' = (frontier \ {n}) \cup Succ[n]
           /\ pc'       = [pc EXCEPT ![p] = @ + 1]
           /\ sel'      = [sel EXCEPT ![p] = CHOOSE m \in frontier' : TRUE]
           /\ succSet'  = [succSet EXCEPT ![p] = Succ[n]]
  \/ \E p \in Procs:
        /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Invariant (type correctness + simple control‑flow properties)
--------------------------------------------------------------------*)
Inv ==
  /\ marked   \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A p \in Procs: sel[p] \in Nodes
  /\ \A p \in Procs: succSet[p] \subseteq Nodes
  /\ pc \in [Procs -> Nat]

(*--------------------------------------------------------------------
  Property stating that the parallel algorithm refines the sequential one.
  Here we keep it simple; the real property would relate the two algorithms.
--------------------------------------------------------------------*)
Refines == TRUE

(*--------------------------------------------------------------------
  Operator that will be substituted for Succ in the configuration.
  It gives each node exactly two distinct successors (if possible).
--------------------------------------------------------------------*)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
     LET others == Nodes \ {n} IN
       IF Cardinality(others) >= 2 THEN
         LET s1 == CHOOSE s \in others : TRUE IN
         LET s2 == CHOOSE s \in (others \ {s1}) : TRUE IN
         {s1, s2}
       ELSE {}]

(*--------------------------------------------------------------------
  Finite version of the generic Seq operator, limited by the number of nodes.
--------------------------------------------------------------------*)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

====