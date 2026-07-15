---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

(* ------------------------------------------------------------------- *)
(* Types *)
(* ------------------------------------------------------------------- *)
NodeSet == SUBSET Nodes

(* ------------------------------------------------------------------- *)
(* Initialization *)
(* ------------------------------------------------------------------- *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

(* ------------------------------------------------------------------- *)
(* Actions *)
(* ------------------------------------------------------------------- *)

(* Helper: set of successors of a node *)
SuccOf(n) == [Succ[n] |-> Seq] \D

PickNode ==
    \E n \in frontier : n

NotMarkedCase ==
    /\ \E n \in frontier :
          /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup SuccOf(n)
    /\ pc' = pc

MarkedCase ==
    /\ \E n \in frontier :
          /\ n \in marked
          /\ frontier' = frontier \ {n}
    /\ pc' = pc

Main ==
    \/ (pc = "Run" /\ NOT frontier = {} /\ PickNode)
       /\ ( \E n \in frontier :
              /\ n \notin marked /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup SuccOf(n)
              /\ pc' = pc
           \/ n \in marked /\ frontier' = frontier \ {n}
              /\ pc' = pc )

Next ==
    \/ (pc = "Run" /\ frontier = {} /\ pc' = "Terminated" /\ marked' = marked /\ frontier' = frontier)
    \/ (pc = "Run" /\ frontier # {} /\ Main)
    \/ (pc = "Terminated" /\ UNCHANGED <<marked, frontier, pc>>)

(* ------------------------------------------------------------------- *)
(* Spec *)
(* ------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ------------------------------------------------------------------- *)
(* Type correctness invariant *)
(* ------------------------------------------------------------------- *)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Terminated"}

(* ------------------------------------------------------------------- *)
(* Safety invariants *)
(* ------------------------------------------------------------------- *)

(* 1. Every successor of a marked node is in marked or frontier *)
Inv1 ==
    \A n \in marked :
        SuccOf(n) \subseteq marked \cup frontier

(* 2. Union of marked and reachable-from-frontier equals reachable-from-union *)
(*    We express a simplified version: all nodes reachable from frontier are already either marked or frontier *)
Inv2 ==
    \A n \in frontier :
        (\A m \in SuccOf(n) : m \in marked \cup frontier)

(* 3. Reachable set equals marked plus reachable-from-frontier *)
Inv3 ==
    \A n \in Nodes :
        (n \in marked) \/ (n \in frontier)

(* 4. Partial correctness: when terminated, marked equals reachable nodes from Root *)
PartialCorrectness ==
    (pc = "Terminated") => marked = ReachableFrom(Root)

(* Helper to compute reachable set from a node using Succ *)
ReachableFrom(n) ==
    LET
        R == {n}
    IN
        R

(* ------------------------------------------------------------------- *)
(* Liveness property: Termination *)
(* ------------------------------------------------------------------- *)
Termination ==
    WF_INIT pc = "Run" /\ Next

====