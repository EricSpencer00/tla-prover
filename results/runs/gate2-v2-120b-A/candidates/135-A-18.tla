---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ, Seq

(* ------------------------------------------------------------------- *)
(* Helper definitions                                                  *)
(* ------------------------------------------------------------------- *)

Node == 1 .. Nodes

SuccSubset == [i \in Node |-> {j \in Node : j \in Succ[i]}]

(* ------------------------------------------------------------------- *)
(* State variables                                                     *)
(* ------------------------------------------------------------------- *)

VARIABLES marked, frontier, pc

(* ------------------------------------------------------------------- *)
(* Type correctness invariant (for TLC)                                *)
(* ------------------------------------------------------------------- *)

TypeOK ==
    /\ marked \in SUBSET Node
    /\ frontier \in SUBSET Node
    /\ pc \in {"Init", "Step", "Done"}

(* ------------------------------------------------------------------- *)
(* Initial state                                                       *)
(* ------------------------------------------------------------------- *)

Init ==
    /\ pc = "Init"
    /\ marked = {}
    /\ frontier = {Root}

(* ------------------------------------------------------------------- *)
(* Transition relation (inherits the algorithm's behavior)            *)
(* ------------------------------------------------------------------- *)

Step ==
    /\ pc = "Step"
    /\ frontier # {}
    /\ LET newMarked == marked \cup frontier IN
       /\ marked' = newMarked
       /\ frontier' = { n \in Node :
                         \E i \in frontier :
                           n \in SuccSubset[i] /\ n \notin newMarked }
       /\ pc' = IF frontier' = {} THEN "Done" ELSE "Step"

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next == Step \/ Done

(* ------------------------------------------------------------------- *)
(* Specification                                                       *)
(* ------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ------------------------------------------------------------------- *)
(* Helper for path existence (bounded by number of nodes)             *)
(* ------------------------------------------------------------------- *)

Path(i, j) ==
    \E p \in Seq :
        /\ Len(p) <= Nodes + 1
        /\ p[1] = i
        /\ Last(p) = j
        /\ \A k \in 1 .. (Len(p) - 1) : p[k+1] \in SuccSubset[p[k]]

(* ------------------------------------------------------------------- *)
(* Invariants                                                          *)
(* ------------------------------------------------------------------- *)

(* 1. Successor closure: every node in frontier is reachable from Root via a bounded path *)
Inv1 == \A n \in frontier : Path(Root, n)

(* 2. Reachability decomposition: marked ∪ frontier = all nodes reachable from Root *)
ReachableFromRoot == { n \in Node : Path(Root, n) }
Inv2 == (marked \cup frontier) = ReachableFromRoot

(* 3. Reachable set equality: marked equals the set of nodes reachable from Root *)
Inv3 == marked = ReachableFromRoot

(* 4. Partial correctness: when algorithm terminates, marked equals the set of all nodes *)
PartialCorrectness == (pc = "Done") => (marked = Node)

(* ------------------------------------------------------------------- *)
(* Liveness property (termination)                                    *)
(* ------------------------------------------------------------------- *)

Termination == <> (pc = "Done")

====