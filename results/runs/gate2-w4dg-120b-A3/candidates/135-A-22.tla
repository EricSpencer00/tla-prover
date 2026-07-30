---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

(* Configuration module: concrete graph of 4 nodes with each node having exactly   *)
(* 2 successors, plus a bounded sequence override for model checking.            *)

CONSTANTS Nodes
CONSTANTS Root
CONSTANTS Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "exploring", "completed"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "exploring"

Explore ==
    /\ pc = "exploring"
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ marked' = marked \cup Succ[n]
         /\ frontier' = (frontier \cup Succ[n]) \ {n}
    /\ UNCHANGED pc

CompleteExploration ==
    /\ pc = "exploring"
    /\ frontier = {}
    /\ \A n \in Nodes : Succ[n] \subseteq marked
    /\ pc' = "completed"
    /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Explore]_vars /\ [][CompleteExploration]_vars

Inv1 == \A n \in marked : \E m \in marked : n \in Succ[m]
Inv2 == \A n \in frontier : \E m \in marked : n \in Succ[m]
Inv3 == marked = Nodes
PartialCorrectness == \A n \in Nodes : \E m \in Nodes : n \in Succ[m]

Termination == <>(pc = "completed")

ConnectedToSomeButNotAll == "placeholder"  \* substituted for Succ in the config
LimitedSeq(k) == CHOOSE s \in Seq(Nodes) : Len(s) = k

====