---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

(* --algorithm variables (for readability) *)
vars == <<marked, frontier, pc>>

(* Type correctness *)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Init", "Mark", "Done"}

(* Successors relation: assumed to be given as a constant relation "Succ". *)
CONSTANT Succ
ASSUME Succ \in [Nodes -> SUBSET Nodes]

(* Initial state *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Init"

(* Actions *)

Mark ==
    /\ pc = "Init"
    /\ marked' = marked \cup frontier
    /\ frontier' = { y \in Nodes : 
                        \E x \in marked : y \in Succ[x] }
    /\ pc' = "Mark"

Done ==
    /\ pc = "Mark"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Mark
    \/ Done
    \/ UNCHANGED <<marked, frontier, pc>>

Spec == Init /\ [][Next]_vars

(* Invariant 1: type correctness plus the property that every successor
   of a marked node is in the marked set or frontier. *)
Inv1 ==
    /\ TypeOK
    /\ \A x \in marked :
          \A y \in Succ[x] : y \in marked \/ y \in frontier

(* Invariant 2: the marked set plus nodes reachable from the frontier equals
   nodes reachable from the union of marked and frontier. *)
ReachableFrom(S) ==
    { y \in Nodes : \E n \in S : y \in Reach[n] }

(* Reach[n] is the set of nodes reachable from n via the Succ relation.
   Defined inductively using the built‑in REACHABLE operator for clarity. *)
Reach == [n \in Nodes |-> REACHABLE {n} (Succ)]

Inv2 ==
    /\ marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

(* Invariant 3: the set of reachable nodes from the root equals the marked set
   plus nodes reachable from the frontier. *)
Inv3 ==
    Reach[Root] = marked \cup ReachableFrom(frontier)

(* The partial‑correctness theorem (stated as a property). *)
PartialCorrectness ==
    /\ pc = "Done"
    /\ marked = Reach[Root]

=============================================================================