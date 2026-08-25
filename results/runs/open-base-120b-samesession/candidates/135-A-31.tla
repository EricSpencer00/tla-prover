---- MODULE MCReachable ----
EXTENDS Sequences, Reachability

CONSTANTS Nodes, Root, Succ

(* Concrete graph with 4 nodes, each node having exactly 2 successors *)
ASSUME Nodes = {1, 2, 3, 4}
ASSUME Root  = 1
ASSUME Succ  = [i \in Nodes |-> 
                  CASE i = 1 -> {2, 3}
                     [] i = 2 -> {3, 4}
                     [] i = 3 -> {1, 4}
                     [] i = 4 -> {1, 2}
                ]

(* Operator that will be substituted for Succ in the configuration *)
ConnectedToSomeButNotAll == Succ

(* Bounded version of Seq for model checking *)
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

(* Aliases to the algorithm's definitions *)
Init == Reachability!Init
Next == Reachability!Next

vars == <<marked, frontier, pc>>

Spec == Init /\ [][Next]_vars

TypeOK == Reachability!TypeOK
Inv1   == Reachability!Inv1
Inv2   == Reachability!Inv2
Inv3   == Reachability!Inv3
PartialCorrectness == Reachability!PartialCorrectness

Termination == <> (frontier = {})

====