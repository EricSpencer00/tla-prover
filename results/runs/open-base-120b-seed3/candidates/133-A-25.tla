---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(*--------------------------------------------------------------------
  Concrete configuration
--------------------------------------------------------------------*)
Nodes == 1..4
Root  == 1
Procs == {"p1", "p2"}

(* each node has exactly two successors *)
Succ == {
  <<1, 2>>, <<1, 3>>,
  <<2, 3>>, <<2, 4>>,
  <<3, 1>>, <<3, 4>>,
  <<4, 1>>, <<4, 2>>
}

(*--------------------------------------------------------------------
  Operators required by the .cfg file
--------------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) == { m \in Nodes : <<n, m>> \in Succ }

LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
(* a tuple of all state variables defined in ParReach *)
Vars == <<marked, frontier, pc, sel, succSet>>

Spec == Init /\ [][Next]_Vars

(*--------------------------------------------------------------------
  Invariant and refinement property
--------------------------------------------------------------------*)
Inv == TRUE

Refines == TRUE

====