---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES Marked, Frontier, pc

(*-----------------------------------------------------------------
  Concrete definitions for the configuration
-----------------------------------------------------------------*)
(* The set of nodes (4 nodes) *)
ASSUME Nodes = {"n1", "n2", "n3", "n4"}

(* The root node *)
ASSUME Root = "n1"

(* Operator that provides a bounded successor relation.
   The .cfg will substitute this operator for the constant Succ. *)
ConnectedToSomeButNotAll(n) ==
  CASE n = "n1" -> {"n2", "n3"}
  [] n = "n2" -> {"n3", "n4"}
  [] n = "n3" -> {"n1", "n4"}
  [] n = "n4" -> {"n1", "n2"}
  [] OTHER   -> {}

(* A finite version of the generic Seq operator.
   The .cfg replaces Seq with this definition (must have one argument). *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*-----------------------------------------------------------------
  Reachability definition using the bounded sequence set
-----------------------------------------------------------------*)
ReachableSet ==
  { n \in Nodes :
      \E s \in Seq(Nodes) :
        /\ Len(s) >= 1
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]]
  }

(*-----------------------------------------------------------------
  Initialization and transition relation
-----------------------------------------------------------------*)
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "run"

Next ==
  \/ /\ Frontier # {}
     /\ \E n \in Frontier :
          /\ Marked' = Marked \cup {n} \cup Succ[n]
          /\ Frontier' = (Frontier \ {n}) \cup (Succ[n] \ Marked)
          /\ pc' = "run"
  \/ /\ Frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<Marked, Frontier>>

Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Inv1 == \A n \in Marked : Succ[n] \subseteq Marked

Inv2 == \A n \in Marked : n \in ReachableSet

Inv3 == Marked = ReachableSet

PartialCorrectness ==
  (pc = "done") => (Frontier = {} /\ Marked = ReachableSet)

(*-----------------------------------------------------------------
  Liveness property
-----------------------------------------------------------------*)
Termination == <> (pc = "done")
====