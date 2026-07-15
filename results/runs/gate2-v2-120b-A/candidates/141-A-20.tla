---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(*  Constants (provided by the .cfg)                                       *)
(***************************************************************************)
CONSTANTS Nodes, Root, Succ, Seq

(***************************************************************************)
(*  Derived sets and functions                                             *)
(***************************************************************************)
NodeSet == Nodes

(* Successor function: Succ[n] is the set of successors of node n *)
Successors == [n \in NodeSet |-> Succ[n]]

(* Helper: the set of nodes reachable from a given set via any number of *)
(* edges, using the standard fixed‑point definition.                       *)
ReachableFrom(S) ==
    LET R == CHOOSE R \in SUBSET NodeSet :
                (S \subseteq R) /\ (R = S \cup UNION {Successors[n] : n \in R})
    IN R

(***************************************************************************)
(*  State variables                                                       *)
(***************************************************************************)
VARIABLES marked, frontier, pc

(* pc values: "Loop" indicates the algorithm is active; "Done" means it has *)
(* terminated.                                                             *)
PCVals == {"Loop", "Done"}

(***************************************************************************)
(*  Initialization                                                         *)
(***************************************************************************)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Loop"

(***************************************************************************)
(*  Actions                                                               *)
(***************************************************************************)
PickNode ==
    frontier

Explore ==
    \E n \in PickNode :
        IF n \notin marked THEN
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Successors[n]
            /\ pc' = "Loop"
        ELSE
            /\ marked' = marked
            /\ frontier' = frontier \ {n}
            /\ pc' = "Loop"

Terminate ==
    /\ frontier = {}
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    /\ pc = "Loop"
    /\ (Explore \/ (frontier = {} /\ pc' = "Done"))
    /\ UNCHANGED Seq   \* Seq is a constant; we keep it unchanged

(***************************************************************************)
(*  Specification                                                         *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(***************************************************************************)
(*  Type correctness invariant                                            *)
(***************************************************************************)
TypeOK ==
    /\ marked \subseteq NodeSet
    /\ frontier \subseteq NodeSet
    /\ pc \in PCVals

(***************************************************************************)
(*  Safety invariants (as described)                                      *)
(***************************************************************************)
Inv1 ==
    \A n \in marked :
        Successors[n] \subseteq marked \cup frontier

Inv2 ==
    \A n \in frontier :
        Successors[n] \subseteq marked \cup frontier

Inv3 ==
    marked \cup frontier = ReachableFrom({Root})

PartialCorrectness ==
    /\ pc = "Done"
    /\ marked = ReachableFrom({Root})

(***************************************************************************)
(*  Liveness property (termination when reachable set is finite)          *)
(***************************************************************************)
Termination ==
    []<>(pc = "Done")

(***************************************************************************)
(*  THEOREMS / PROPERTIES (names must match the .cfg)                     *)
(***************************************************************************)
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness

=============================================================================