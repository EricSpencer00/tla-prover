---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Constants required by the reference .cfg
--------------------------------------------------------------------*)
CONSTANTS
    Nodes,      \* The set of all node identifiers (finite)
    Root,       \* The distinguished start node
    Succ,       \* Function: Nodes -> SUBSET Nodes, the successors of each node
    Seq         \* Upper bound on the length of any path (used for path sequences)

(*--------------------------------------------------------------------
  Derived constants for convenience
--------------------------------------------------------------------*)
Node == Nodes

(*--------------------------------------------------------------------
  Variables inherited from the sequential reachability algorithm
--------------------------------------------------------------------*)
VARIABLES
    marked,     \* Set of nodes already known to be reachable
    frontier,  \* Set of nodes whose successors are being explored next
    pc          \* Program counter (abstract representation of algorithm phase)

(*--------------------------------------------------------------------
  Type invariant (TypeOK) required by the .cfg
--------------------------------------------------------------------*)
TypeOK ==
    /\ marked \in SUBSET Node
    /\ frontier \in SUBSET Node
    /\ pc \in {"Init", "Expand", "Done"}

(*--------------------------------------------------------------------
  Initial state (Init) – corresponds to the algorithm's INIT
--------------------------------------------------------------------*)
Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "Expand"

(*--------------------------------------------------------------------
  One step of the algorithm (Expand) – corresponds to the algorithm's NEXT
--------------------------------------------------------------------*)
Expand ==
    /\ pc = "Expand"
    /\ LET newFrontier == { y \in Node : 
                              \E x \in frontier : y \in Succ[x] /\ y \notin marked } IN
       /\ marked' = marked \cup frontier
       /\ frontier' = newFrontier
       /\ pc' = IF newFrontier = {} THEN "Done" ELSE "Expand"

Done ==
    /\ pc = "Done"
    /\ UNCHANGED << marked, frontier, pc >>

(*--------------------------------------------------------------------
  NEXT relation – nondeterministic choice of applicable action
--------------------------------------------------------------------*)
Next ==
    \/ Expand
    \/ Done

(*--------------------------------------------------------------------
  Specification formula required by the .cfg
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Algorithm invariants required by the .cfg
--------------------------------------------------------------------*)

(* Inv1: Successor closure – every node in frontier has a predecessor in marked *)
Inv1 ==
    \A y \in frontier :
        \E x \in marked : y \in Succ[x]

(* Inv2: Reachability decomposition – marked is exactly the set of nodes that have a path from Root of length ≤ Seq *)
Paths == { seq \in Seq(0 .. Seq) : 
            /\ Len(seq) >= 1
            /\ seq[1] = Root
            /\ \A i \in 1 .. Len(seq)-1 : seq[i+1] \in Succ[seq[i]] }

Inv2 ==
    marked = { n \in Node : \E seq \in Paths : seq[Len(seq)] = n }

(* Inv3: Reachable set equality – the algorithm's frontiers eventually become empty only when all reachable nodes are marked *)
Inv3 ==
    (frontier = {}) => (marked = { n \in Node : \E seq \in Paths : seq[Len(seq)] = n })

(* PartialCorrectness – when the algorithm terminates, marked equals the reachable set from Root *)
PartialCorrectness ==
    pc = "Done" => (marked = { n \in Node : \E seq \in Paths : seq[Len(seq)] = n })

(*--------------------------------------------------------------------
  Liveness property required by the .cfg
--------------------------------------------------------------------*)
Termination == <> (pc = "Done")

(*--------------------------------------------------------------------
  Theorems (optional, but useful for TLC)
--------------------------------------------------------------------*)
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination

====