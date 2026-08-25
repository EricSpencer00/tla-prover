---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, SeqReachability, ReachabilityProofs

CONSTANTS Nodes, Root, Edge

VARIABLES Marked, Frontier, PC

(* Successor relation derived from the graph edges *)
Succ(n) == { m \in Nodes : <<n, m>> \in Edge }

(* ReachableFrom(S) returns the set of nodes reachable from any node in S *)
RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  IF S = {} THEN {}
  ELSE
    LET NextS == { m \in Nodes : \E n \in S : <<n, m>> \in Edge }
    IN S \/ ReachableFrom(NextS)

(* Initial state *)
INIT ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ PC = "start"

(* Example action: add a successor of a marked node to the frontier *)
AddSuccessor ==
  /\ PC = "start"
  /\ \E n \in Marked, m \in Succ(n) :
        /\ m \notin Marked
        /\ m \notin Frontier
        /\ Marked' = Marked
        /\ Frontier' = Frontier \/ {m}
        /\ PC' = "start"
  \/ /\ Marked' = Marked
      /\ Frontier' = {}
      /\ PC' = "done"

(* Overall next-state relation *)
NEXT ==
  \/ AddSuccessor

(* Invariant 1: type correctness and successor property *)
Inv1 ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ \A n \in Marked : \A m \in Succ(n) : m \in Marked \/ Frontier

(* Invariant 2: marked ∪ reachable(frontier) = reachable(marked ∪ frontier) *)
Inv2 ==
  (Marked \/ ReachableFrom(Frontier)) = ReachableFrom(Marked \/ Frontier)

(* Invariant 3: reachable from root = marked ∪ reachable(frontier) *)
Inv3 ==
  ReachableFrom({Root}) = Marked \/ ReachableFrom(Frontier)

(* Specification combining init and next *)
Spec == INIT /\ [][NEXT]_<<Marked, Frontier, PC>>

(* Set of invariants for the model checker *)
INVARIANTS == {Inv1, Inv2, Inv3}

(* Properties to be checked; here we include the invariants as part of the overall property *)
PROPERTIES == Spec /\ Inv1 /\ Inv2 /\ Inv3

====