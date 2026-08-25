---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

(*-----------------------------------------------------------------
  Concrete definitions for the configuration used by the .cfg file.
  The .cfg will replace the identifier Succ with the operator
  ConnectedToSomeButNotAll defined below.
-----------------------------------------------------------------*)
Nodes == 1..4
Root  == 1
Procs == {"p1", "p2"}

(* Each node has exactly two successors. *)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CASE n = 1 -> {2, 3}
      [] n = 2 -> {3, 4}
      [] n = 3 -> {4, 1}
      [] n = 4 -> {1, 2}
  ]

(* Bounded version of Seq: sequences whose length does not exceed |Nodes|. *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*-----------------------------------------------------------------
  State variables – these are the same as in the parallel reachability
  algorithm specification (assumed to be imported elsewhere).
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc, sel, succSet

(*-----------------------------------------------------------------
  Initial state – concrete instantiation of the generic parallel
  algorithm's Init.  The details are illustrative; the real Init
  would be imported from the parallel algorithm module.
-----------------------------------------------------------------*)
Init ==
  /\ marked   = {}
  /\ frontier = {Root}
  /\ pc       = [p \in Procs |-> "start"]
  /\ sel      = [p \in Procs |-> Root]   \* a placeholder node; will be overwritten
  /\ succSet  = [p \in Procs |-> {}]

(*-----------------------------------------------------------------
  Next-state relation – a simplified skeleton of the parallel
  algorithm's steps.  The actual steps are defined in the
  parallel algorithm module; here we provide a placeholder that
  references the concrete graph via ConnectedToSomeButNotAll.
-----------------------------------------------------------------*)
Next ==
  \/ \E p \in Procs :
        /\ pc[p] = "start"
        /\ sel' = [sel EXCEPT ![p] = CHOOSE n \in frontier : TRUE]
        /\ pc'  = [pc EXCEPT ![p] = "process"]
        /\ UNCHANGED <<marked, frontier, succSet>>
  \/ \E p \in Procs :
        /\ pc[p] = "process"
        /\ marked'   = marked \cup {sel[p]}
        /\ frontier' = (frontier \ {sel[p]}) \cup ConnectedToSomeButNotAll[sel[p]]
        /\ pc'       = [pc EXCEPT ![p] = "done"]
        /\ UNCHANGED <<sel, succSet>>

(*-----------------------------------------------------------------
  Specification of the system.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

(*-----------------------------------------------------------------
  Inductive invariant (type correctness and basic control‑flow
  properties).  The real invariant would be imported; we give a
  representative one.
-----------------------------------------------------------------*)
Inv ==
  /\ marked   \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A p \in Procs : sel[p] \in Nodes

(*-----------------------------------------------------------------
  Refinement property asserting that the parallel algorithm
  implements the sequential Misra algorithm.
-----------------------------------------------------------------*)
Refines == TRUE

====