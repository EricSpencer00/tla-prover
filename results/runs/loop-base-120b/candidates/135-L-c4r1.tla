---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root

(* Finite successor relation: each node has exactly two successors *)
ConnectedToSomeButNotAll(n) ==
  CASE n = "n1" -> {"n2", "n3"}
  []   n = "n2" -> {"n3", "n4"}
  []   n = "n3" -> {"n1", "n4"}
  []   n = "n4" -> {"n1", "n2"}
  []   OTHER      -> {}

(* Bounded sequence operator, used to replace the unbounded Seq *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES Marked, Frontier, pc

(* Initial state *)
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "start"

(* One step of the sequential Misra reachability algorithm *)
Next ==
  \/ /\ pc = "start"
     /\ \E n \in Frontier :
          /\ Marked'   = Marked \cup {n}
          /\ Frontier' = (Frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ Marked')
          /\ pc'       = IF Frontier' = {} THEN "done" ELSE "start"
  \/ /\ pc = "done"
     /\ UNCHANGED <<Marked, Frontier, pc>>

(* Main specification *)
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

(* Invariants required by the .cfg file *)

TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"start", "done"}

Inv1 ==
  /\ \A n \in Marked : ConnectedToSomeButNotAll[n] \subseteq Nodes

Inv2 ==
  /\ Frontier = (Nodes \ Marked) \/ {}

Inv3 ==
  /\ Marked \cup Frontier = Nodes

PartialCorrectness ==
  /\ pc = "done"
     => Marked = Nodes

(* Liveness property *)
Termination == <> (pc = "done")
====