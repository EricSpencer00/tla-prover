---- MODULE MCReachable ----
EXTENDS Reachable

ConnectedToSomeButNotAll ==
  [n \in Nodes |-> {n1, n2} ]

LimitedSeq(S) == UNION {
  [1 .. len -> S]
  : len \in 0 .. Cardinality(Nodes)
}

====