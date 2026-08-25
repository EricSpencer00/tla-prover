---- MODULE MCParReach ----
EXTENDS ParReach, Sequences

CONSTANTS Nodes, Root, Procs, Succ

ASSUME Nodes = {"n1", "n2", "n3", "n4"}
ASSUME Root = "n1"
ASSUME Root \in Nodes
ASSUME Procs = {"p1", "p2"}

ConnectedToSomeButNotAll(node) ==
  CASE node = "n1" -> {"n2", "n3"}
  [] node = "n2" -> {"n3", "n4"}
  [] node = "n3" -> {"n4", "n1"}
  [] node = "n4" -> {"n1", "n2"}
  END CASE

LimitedSeq(E) == { s \in Seq(E) : Len(s) <= Cardinality(Nodes) }

Spec == ParReach!Spec
Inv == ParReach!Inv
Refines == ParReach!Refines
====