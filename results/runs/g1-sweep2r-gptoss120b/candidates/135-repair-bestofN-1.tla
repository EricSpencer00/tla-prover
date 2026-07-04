---- MODULE MCReachable ----
EXTENDS Reachable

(*
  Choose a successor function that maps each node to a subset of nodes
  of exactly two elements.
*)
ConnectedToSomeButNotAll ==
  CHOOSE succ \in [Nodes -> SUBSET Nodes] :
    \A n \in Nodes : Cardinality(succ[n]) = 2

(*
  The set of all (finite) sequences over S whose length is at most
  the number of nodes.  Each sequence is represented as a function whose
  domain is 1..len for some len in 0..|Nodes|.
*)
LimitedSeq(S) ==
  { f : \E len \in 0 .. Cardinality(Nodes) : f \in [1 .. len -> S] }

====