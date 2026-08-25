---- MODULE MCReachable ----
EXTENDS MisraReachability, Sequences

CONSTANTS Nodes, Root, Succ

(* Concrete graph definitions *)
Nodes == {1, 2, 3, 4}
Root  == 1

(* Operator providing exactly two successors per node, to be used in place of Succ *)
ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2, 3}
       [] n = 2 -> {3, 4}
       [] n = 3 -> {4, 1}
       [] n = 4 -> {1, 2}
       [] OTHER -> {}

(* Bounded sequence operator for model checking *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Specification *)
Spec ==
  Init /\ [][Next]_{<<marked, frontier, pc>>}

(* Termination property *)
Termination == <> (pc = "Done")

====