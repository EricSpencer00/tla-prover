---- MODULE ReachableProofs ----
EXTENDS SequentialReachability, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

(* Assume that the imported modules define the following constants and functions:
   Succ: Nodes -> SUBSET Nodes   -- successor relation
   Reachable: SUBSET Nodes -> SUBSET Nodes  -- set of nodes reachable from a set
   Init, Next                          -- transition relation of the algorithm
*)

Variables == <<Marked, Frontier, pc>>

(* Type correctness and basic closure invariant *)
TypeOK == Marked \subseteq Nodes /\ Frontier \subseteq Nodes
          /\ \A s \in Marked : Succ[s] \subseteq Nodes

Invariant1 == TypeOK /\ \A s \in Marked : Succ[s] \subseteq Marked \cup Frontier

(* Graph-theoretic invariants *)
Invariant2 == Marked \cup Reachable(Frontier) = Reachable(Marked \cup Frontier)

Invariant3 == Reachable({Root}) = Marked \cup Reachable(Frontier)

Spec == Init /\ [][Next]_Variables

THEOREM FinalCorrectness ==
  Spec => [] (pc = "Done" => Marked = Reachable({Root}))

====