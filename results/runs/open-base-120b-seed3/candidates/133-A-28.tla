---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete definitions for the configuration *)
Nodes == 1..4
Root == 1
Procs == 1..2

Succ == [n \in Nodes |-> 
            CASE n = 1 -> {2,3}
               [] n = 2 -> {3,4}
               [] n = 3 -> {4,1}
               [] OTHER -> {1,2}]

(* Operator that the .cfg substitutes for Succ *)
ConnectedToSomeButNotAll == Succ

(* Bounded version of Seq, limited to length ≤ |Nodes| *)
LimitedSeq(S) ==
    LET maxLen == Cardinality(Nodes) IN
    { s \in Seq(S) : Len(s) <= maxLen }

VARIABLES marked, frontier, pc, selected, succSet

(* Import the parallel reachability algorithm specification *)
INSTANCE ParallelReach AS PR

Init == PR!Init
Next == PR!Next

Spec == Init /\ [][Next]_<<marked, frontier, pc, selected, succSet>>

Inv == PR!Inv

Refines == PR!Refines

====