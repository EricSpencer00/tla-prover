---- MODULE MCParReach ----
EXTENDS FiniteSets, Sequences, Naturals, ParReach
CONSTANTS Nodes, Root, Procs, Succ

(*--- Concrete definitions for the configuration ---*)
ASSUME Nodes = {n1, n2, n3, n4}
ASSUME Root = n1
ASSUME Procs = {p1, p2}

(*--- Graph: each node has exactly two successors ---*)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CASE n = n1 -> {n2, n3}
        [] n = n2 -> {n3, n4}
        [] n = n3 -> {n1, n4}
        [] n = n4 -> {n1, n2} ]

(*--- Finite sequence operator bounded by the number of nodes ---*)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*--- Specification, invariant and refinement property ---*)
Spec == Init /\ [][Next]_vars

Inv == ParReach!Inv

Refines == ParReach!Refines

====