---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets

(* ----------------------------------------------------------------------
   Constants
   ---------------------------------------------------------------------- *)
CONSTANTS Nodes, Root

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES marked, frontier, pc

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

NodeSet == Nodes
RootNode == Root

(* ----------------------------------------------------------------------
   Algorithm actions (as described in the sequential reachability module)
   ---------------------------------------------------------------------- *)

Init ==
    /\ marked = {}
    /\ frontier = {RootNode}
    /\ pc = "loop"

StepMark ==
    /\ pc = "loop"
    /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup
                        { m \in NodeSet : m \notin marked \cup frontier
                                           /\ \E k \in marked \cup {n} : m \in Succ[k] }
        /\ pc' = "loop"

StepDone ==
    /\ pc = "loop"
    /\ frontier = {}
    /\ marked' = marked
    /\ frontier' = frontier
    /\ pc' = "done"

Next ==
    \/ StepMark
    \/ StepDone

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)

(* Invariant 1: type correctness and successor condition *)
Inv1 ==
    /\ marked \subseteq NodeSet
    /\ frontier \subseteq NodeSet
    /\ \A s \in marked :
        \A t \in Succ[s] :
            t \in marked \/ t \in frontier

(* Invariant 2: reachable-from relation equivalence (Lemma 1) *)
Inv2 ==
    (\A x \in marked \cup frontier :
        ReachableFrom(marked \cup frontier, x) =
        ReachableFrom(marked, x) \cup ReachableFrom(frontier, x))

(* Invariant 3: marked set plus reachable-from frontier equals reachable set *)
Inv3 ==
    ReachableFrom(NodeSet, RootNode) =
    marked \cup ReachableFrom(frontier, RootNode)

(* ----------------------------------------------------------------------
   Theorem (partial correctness)
   ---------------------------------------------------------------------- *)

THEOREM TerminationPartialCorrectness ==
    Spec => [] (pc = "done" => marked = ReachableFrom(NodeSet, RootNode))

====