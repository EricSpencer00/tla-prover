---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(*  Constants (to be instantiated in the .cfg file)                        *)
(*  Nodes   : The universe of graph nodes                                   *)
(*  Root    : The root node from which reachability is computed            *)
(*  Succ    : Successor relation; Succ[n] is the set of successors of n    *)
(*  Seq     : A totally ordered finite sequence containing all nodes (used *)
(*            to define reachability as the least fixed point)             *)
(***************************************************************************)

CONSTANTS Nodes, Root, Succ, Seq

(***************************************************************************)
(*  State variables                                                       *)
(***************************************************************************)

VARIABLES marked, frontier, pc

(* Types for documentation *)
MarkedSet == SUBSET Nodes
FrontierSet == SUBSET Nodes
PcValues == {"Running", "Done"}

(***************************************************************************)
(*  Initial state                                                         *)
(***************************************************************************)

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"
    /\ TypeOK

(***************************************************************************)
(*  Main action                                                          *)
(***************************************************************************)

Next ==
    \/ /\ pc = "Running"
         /\ frontier # {}
         /\ \E n \in frontier :
                /\ IF n \in marked THEN
                       /\ marked' = marked
                       /\ frontier' = frontier \ {n}
                   ELSE
                       /\ marked' = marked \cup {n}
                       /\ frontier' = frontier \cup Succ[n]
                /\ pc' = "Running"
                /\ TypeOK
    \/ /\ pc = "Running"
         /\ frontier = {}
         /\ pc' = "Done"
         /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "Done"
         /\ UNCHANGED <<marked, frontier, pc>>

(***************************************************************************)
(*  Specification                                                         *)
(***************************************************************************)

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(***************************************************************************)
(*  Type correctness invariant                                            *)
(***************************************************************************)

TypeOK == 
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in PcValues

(***************************************************************************)
(*  Reachability definitions                                             *)
(***************************************************************************)

(* Reachable from a set of nodes using the successor relation *)
ReachableFrom(S) ==
    UNION { Succ[n] : n \in S } \cup S

(* The least fixed point of ReachableFrom starting from the root *)
REACHABLE ==
    CHOOSE R \in SUBSET Nodes :
        /\ Root \in R
        /\ ReachableFrom(R) = R

(***************************************************************************)
(*  Safety invariants                                                     *)
(***************************************************************************)

(* Inv1: Every successor of a marked node is either marked or in the frontier *)
Inv1 == 
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* Inv2: The union of marked and the nodes reachable from frontier is closed *)
Inv2 ==
    marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

(* Inv3: The set of nodes reachable from the root equals marked plus those reachable from frontier *)
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

(* Partial correctness: when the algorithm is done, marked equals the set of nodes reachable from the root *)
PartialCorrectness ==
    pc = "Done" => marked = ReachableFrom({Root})

(***************************************************************************)
(*  Liveness property (termination)                                       *)
(***************************************************************************)

Termination == 
    []<>(pc = "Done")

=============================================================================