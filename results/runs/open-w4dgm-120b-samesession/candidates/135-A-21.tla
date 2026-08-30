---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

(* A model-checking configuration for the Misra reachability algorithm.      *)
(* It inherits the algorithm's state variables and actions, and adds the      *)
(* concrete graph structure and a bounded-sequence override needed for        *)
(* exhaustive checking.                                                       *)

(* Configuration-provided constants: the node set, the start node, and the    *)
(* successor relation (every node has exactly two successors).                *)
CONSTANT Nodes
CONSTANT Root
CONSTANT Succ

VARIABLES marked, frontier, pc

\* The algorithm's actions are unchanged; only the graph and the seq bound    \* are provided here.
Init == /\ marked = {Root}
        /\ frontier = {Root}
        /\ pc = "idle"

StartDFS == /\ pc = "idle"
            /\ frontier # {}
            /\ pc' = "searching"
            /\ UNCHANGED <<marked, frontier>>

Explore(v) == /\ pc = "searching"
              /\ v \in frontier
              /\ frontier' = frontier \ {v}
              /\ marked' = marked \cup ConnectedToSomeButNotAll[v]
              /\ UNCHANGED pc

Backtrack == /\ pc = "searching"
             /\ frontier = {}
             /\ pc' = "done"
             /\ UNCHANGED <<marked, frontier>>

Halt == /\ pc = "done"
        /\ UNCHANGED <<marked, frontier, pc>>

Next == StartDFS \/ Backtrack \/ Halt \/ (\E v \in Nodes : Explore(v))

vars == <<marked, frontier, pc>>

Spec == Init /\ [][Next]_vars
        /\ (\A v \in Nodes : SF_vars(Explore(v)))
        /\ WF_vars(Halt)

(* Configuration: a deterministic bounded-arity neighbor set for each node. *)
ConnectedToSomeButNotAll ==
  [v \in Nodes |-> IF v + 2 <= Cardinality(Nodes) THEN {v + 1, v + 2} ELSE {Root}]

(* Sequences are finite up to the number of nodes -- a bounded truncation.  *)
LimitedSeq == [S \in SUBSET Nodes |-> CHOOSE f \in [1..Cardinality(Nodes) -> S] :
                              \A i \in 1..Cardinality(Nodes) : f[i] \in S]

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "searching", "done"}

(* Successor closure of the marked set: every marked node's neighbor is     *)
(* marked, so no explored node points outside the visited region.            *)
Inv1 ==
  \A v \in Nodes : (v \in marked) => (ConnectedToSomeButNotAll[v] \subseteq marked)

(* Reachable nodes are saturated by the frontier: every reachable node not  *)
(* yet marked is still waiting in the frontier.                              *)
Inv2 ==
  \A v \in Nodes : (v \in Reachable(Root, Succ) /\ v \notin marked) => v \in frontier

(* Every marked node is reachable from the start.                           *)
Inv3 ==
  \A v \in Nodes : (v \in marked) => Reachable(Root, Succ, v)

(* The marked set is exactly the reachable set: completeness and soundness.  *)
PartialCorrectness ==
  \A v \in Nodes : (v \in marked) <=> Reachable(Root, Succ, v)

Termination == <>(pc = "done")

====