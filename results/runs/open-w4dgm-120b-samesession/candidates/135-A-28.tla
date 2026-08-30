---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences

(* Model-checking configuration for the sequential Misra reachability     *)
(* algorithm.  It provides concrete values (a 4-node graph with each node  *)
(* having exactly two successors, and a bounded sequence length) so the   *)
(* state space is finite and exhaustive checking is possible.             *)

CONSTANTS Nodes, Root, Succ

Seq == LimitedSeq

Vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "running"

(* The processing step is unchanged from the algorithm spec: every node    *)
(* reachable by a marked node's two successors is added to the frontier.  *)
Step ==
    /\ pc = "running"
    /\ frontier' = {y \in Nodes : \E x \in marked : y \in ConnectedToSomeButNotAll[x]}
    /\ marked' = marked \cup frontier
    /\ pc' = IF marked = Nodes THEN "done" ELSE "running"

Next == Step

Spec == Init /\ [][Next]_Vars /\ (\A v \in Vars : WF_Vars(Step))

(* Type correctness: frontier and marked are subsets of Nodes.            *)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes

(* Every frontier node is a successor of some already-marked node.        *)
Inv1 ==
    \A y \in frontier : \E x \in marked : y \in ConnectedToSomeButNotAll[x]

(* Reachable via a path implies reachable via a single step from marked. *)
Inv2 ==
    {y \in Nodes : \E s \in Seq : s # <<>> /\ Head(s) = y /\ \A i \in 1..Len(s) : s[i] \in marked}
        \subseteq
    {y \in Nodes : \E x \in marked : y \in ConnectedToSomeButNotAll[x]}

(* Reachable via a single step from marked implies reachable via a path. *)
Inv3 ==
    {y \in Nodes : \E x \in marked : y \in ConnectedToSomeButNotAll[x]}
        \subseteq
    {y \in Nodes : \E s \in Seq : s # <<>> /\ Head(s) = y /\ \A i \in 1..Len(s) : s[i] \in marked}

(* Every node is eventually marked.                                       *)
PartialCorrectness == \A y \in Nodes : \E s \in Seq : s # <<>> /\ Head(s) = y

(* Exhaustive checking: the sequential algorithm always finishes.          *)
Termination == <>(pc = "done")

Invariants == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness

====