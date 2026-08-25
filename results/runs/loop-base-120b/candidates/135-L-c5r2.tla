---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(*-----------------------------------------------------------------
  Configuration operator that will replace Succ via the .cfg file.
  For each node it returns exactly two distinct successors chosen
  nondeterministically from the other nodes.
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      LET others == Nodes \ {n} IN
        IF Cardinality(others) >= 2 THEN
          LET x == CHOOSE a \in others : TRUE IN
            { x, CHOOSE b \in others \ {x} : TRUE }
        ELSE others
   ]

(*-----------------------------------------------------------------
  Finite version of Seq for model checking (kept for compatibility;
  not used in the final definition of ReachableSet).
-----------------------------------------------------------------*)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES Marked, Frontier, pc

(*-----------------------------------------------------------------
  ReachableSet defined by a bounded iterative construction.
  The iteration depth is bounded by the number of nodes, guaranteeing
  finiteness.
-----------------------------------------------------------------*)
RECURSIVE Reachability(_)
Reachability(k) ==
  IF k = 0 THEN {Root}
  ELSE
    LET prev == Reachability(k-1) IN
      prev \cup { n \in Nodes : \E m \in prev : n \in Succ[m] }

ReachableSet == Reachability(CARDINALITY(Nodes))

(*-----------------------------------------------------------------
  Initialization.
-----------------------------------------------------------------*)
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "run"

(*-----------------------------------------------------------------
  Next-state relation.
-----------------------------------------------------------------*)
Next ==
  \/ /\ pc = "run"
     /\ Frontier # {}
     /\ \E n \in Frontier :
          /\ Marked'   = Marked \cup {n}
          /\ Frontier' = (Frontier \ {n}) \cup (Succ[n] \ Marked)
          /\ pc'       = IF Frontier' = {} THEN "done" ELSE "run"
  \/ /\ pc = "done"
     /\ UNCHANGED <<Marked, Frontier, pc>>

(*-----------------------------------------------------------------
  Specification.
-----------------------------------------------------------------*)
Spec ==
  Init /\ [][Next]_<<Marked, Frontier, pc>>

(*-----------------------------------------------------------------
  Invariants.
-----------------------------------------------------------------*)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Inv1 == \A n \in Marked : Succ[n] \subseteq Marked \cup Frontier

Inv2 == Marked \cup Frontier = ReachableSet

Inv3 == Marked = ReachableSet

PartialCorrectness == (pc = "done") => Marked = ReachableSet

(*-----------------------------------------------------------------
  Liveness property: termination.
-----------------------------------------------------------------*)
Termination == <> (pc = "done")

=============================================================================