---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Constants required by the .cfg file
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ, Seq

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
NodeSet == Nodes

(* Succ is a function from a node to a finite set of successor nodes.
   The .cfg file must supply a concrete definition, e.g.,
   Succ == [n \in Nodes |-> { ... }].
*)

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

(*-----------------------------------------------------------------
  Type correctness (TypeOK) invariant
-----------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Running", "Done"}

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"

(*-----------------------------------------------------------------
  Helper: reachability from a set of starting nodes
-----------------------------------------------------------------*)
ReachFrom(S) ==
    IF S = {} THEN {}
    ELSE
        LET
            step(T) == T \cup { y \in Nodes : \E x \in T : y \in Succ[x] }
            iter(T, n) == IF n = 0 THEN T ELSE iter(step(T), n - 1)
        IN
            UNION { iter(step(S), i) : i \in Nat }

(*-----------------------------------------------------------------
  Main action (single process) with two nondeterministic cases
-----------------------------------------------------------------*)
Main ==
    /\ pc = "Running"
    /\ frontier # {}
    /\ \E n \in frontier :
        IF n \notin marked THEN
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ pc' = pc
        ELSE
            /\ marked' = marked
            /\ frontier' = frontier \ {n}
            /\ pc' = pc

(*-----------------------------------------------------------------
  Termination condition: when frontier becomes empty, we move to Done
-----------------------------------------------------------------*)
Terminate ==
    /\ pc = "Running"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED << marked, frontier >>

(*-----------------------------------------------------------------
  Stuttering step when already Done
-----------------------------------------------------------------*)
DoneStutter ==
    /\ pc = "Done"
    /\ UNCHANGED << marked, frontier, pc >>

Next ==
    \/ Main
    \/ Terminate
    \/ DoneStutter

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Invariants from the description
-----------------------------------------------------------------*)
(* 1. Every successor of a marked node is in marked or frontier *)
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* 2. The union of marked and nodes reachable from frontier equals the
      nodes reachable from the union of marked and frontier *)
Inv2 ==
    ReachFrom(marked \cup frontier) = marked \cup ReachFrom(frontier)

(* 3. Nodes reachable from Root equal marked plus nodes reachable from frontier *)
Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

(* Partial correctness: when algorithm has terminated, marked = reachable set *)
PartialCorrectness ==
    /\ pc = "Done"
    /\ marked = ReachFrom({Root})

(*-----------------------------------------------------------------
  Liveness (termination) property: if reachable set is finite, eventually Done
-----------------------------------------------------------------*)
Termination == \<>\<>(pc = "Done")

=============================================================================