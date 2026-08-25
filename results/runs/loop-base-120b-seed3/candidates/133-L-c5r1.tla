---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets, ParReach

CONSTANTS Nodes, Root, Procs, Succ

\* Concrete configuration constants
Nodes == 1..4
Root  == 1
Procs == 1..2

\* Succ will be replaced by ConnectedToSomeButNotAll in the .cfg file.
\* We keep Succ abstract here (no definition) so the substitution can supply its value.

ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CASE n = 1 -> {2,3}
      [] n = 2 -> {3,4}
      [] n = 3 -> {4,1}
      [] n = 4 -> {1,2}
  ]

\* Finite version of Seq (bounded by the number of nodes)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* Specification, initial predicate and next-state relation are taken from the
\* parallel algorithm module.
Spec == ParReach!Spec
Init == ParReach!Init
Next == ParReach!Next

\* Invariant and refinement property required by the .cfg file.
Inv == ParReach!Inv
Refines == ParReach!Refines
====