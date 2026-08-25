---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc

(* Graph edges: Succ maps each node to the set of its successors *)
CONSTANT Succ
ASSUME Succ \in [Nodes -> SUBSET Nodes]

(* Relation derived from Succ, needed for the transitive‑closure operator TC *)
Rel == { <<n, m>> : n \in Nodes /\ m \in Succ[n] }

(* Reachable nodes from a set S, using the transitive closure of Rel *)
REACHABLE(S) == S \cup TC(Rel, S)

(* Initial state of the sequential reachability algorithm *)
INIT ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "start"

(* One step of the algorithm.  The details are kept simple but capture the
   essential behaviour: take a node from the frontier, add it to the marked
   set, and enlarge the frontier with its successors that are not yet known. *)
NEXT ==
    \/ /\ pc = "explore"
       /\ \E n \in frontier :
            /\ marked'   = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ (marked \cup frontier))
            /\ pc'       = "explore"
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

(* The overall specification *)
Spec == INIT /\ [][NEXT]_<<marked, frontier, pc>>

(* --- Invariants ----------------------------------------------------------- *)

(* Invariant 1 : type correctness and the successor condition *)
Inv1 ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked :
         \A s \in Succ[n] :
             s \in marked \/ s \in frontier

(* Invariant 2 : marked ∪ reachable(frontier) = reachable(marked ∪ frontier) *)
Inv2 ==
    marked \cup REACHABLE(frontier) = REACHABLE(marked \cup frontier)

(* Invariant 3 : reachable from the root equals marked ∪ reachable(frontier) *)
Inv3 ==
    REACHABLE({Root}) = marked \cup REACHABLE(frontier)

INVARIANTS == { Inv1, Inv2, Inv3 }

(* Additional properties to be checked – here we simply expose the invariants *)
PROPERTIES == INVARIANTS

====