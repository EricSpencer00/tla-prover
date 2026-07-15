---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, PC

(* Successor function: each node reaches every other node (excluding itself) *)
Succ == [n \in Nodes |-> {y \in Nodes : y # n}]

(* Helper: nodes reachable from set X via Succ *)
ReachableSet(X) ==
    { y \in Nodes :
        \E seq \in Seq :
            /\ seq[1] \in X
            /\ y = seq[Len(seq)]
            /\ \A i \in 1..Len(seq)-1 : seq[i+1] \in Succ(seq[i]) }

(* Type correctness *)
TypeOK ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ PC \in Nodes \cup {0}
    /\ Root \in Nodes

(* Initial state *)
Init ==
    /\ TypeOK
    /\ Marked = {Root}
    /\ Frontier = {Root}
    /\ PC = Root

(* Actions *)
ProcessNode ==
    /\ Frontier # {}
    /\ \E n \in Frontier :
        /\ Marked' = Marked
        /\ Frontier' = (Frontier \ {n}) \cup (Succ(n) \ Marked)
        /\ PC' = n

Terminate ==
    /\ Frontier = {}
    /\ Marked' = Marked
    /\ Frontier' = Frontier
    /\ PC' = 0

Next ==
    ProcessNode \/ Terminate

Spec == Init /\ [][Next]_<<Marked, Frontier, PC>>

(* Invariants *)
INV1 ==
    /\ TypeOK
    /\ \A n \in Marked : Succ(n) \subseteq Marked \cup Frontier

INV2 ==
    Marked \cup ReachableSet(Frontier) = ReachableSet(Marked \cup Frontier)

INV3 ==
    ReachableSet({Root}) = Marked \cup ReachableSet(Frontier)

(* Partial correctness *)
PartialCorrectness ==
    [] (Frontier = {} => Marked = ReachableSet({Root}))

====