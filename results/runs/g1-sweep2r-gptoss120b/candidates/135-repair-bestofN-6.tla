---- MODULE MCReachable ----
EXTENDS Reachable

ConnectedToSomeButNotAll ==
  [ n1 |-> {n2, n3},
    n2 |-> {n2, n2},
    n3 |-> {n3, n3},
    n4 |-> {n4, n4} ]

LimitedSeq(S) == UNION {
  [1 .. len -> S]
  : len \in 0 .. Cardinality(Nodes)
}
====