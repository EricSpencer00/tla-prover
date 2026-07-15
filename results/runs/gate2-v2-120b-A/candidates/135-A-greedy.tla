---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants required by the .cfg file
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ, Seq

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Node == Nodes

(*-----------------------------------------------------------------
  State variables (inherited from the sequential reachability algorithm)
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
MarkedSet == marked
FrontierSet == frontier

(*-----------------------------------------------------------------
  Initial state (inherited, instantiated with concrete graph)
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Init"

(*-----------------------------------------------------------------
  Actions (inherited, unchanged)
-----------------------------------------------------------------*)
Step ==
    /\ pc = "Init"
    /\ frontier # {}
    /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
        /\ pc' = "Step"

Done ==
    /\ pc = "Step"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Step
    \/ Done

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Node
    /\ frontier \subseteq Node
    /\ pc \in {"Init", "Step", "Done"}

(* Inv1: Successor closure – every node in frontier has a successor in the graph *)
Inv1 ==
    \A n \in frontier : Succ[n] # {}

(* Inv2: Reachability decomposition – marked ∪ frontier = nodes reachable from Root *)
ReachableFromRoot ==
    { n \in Node :
        \E s \in Seq :
            Len(s) > 0 /\ s[1] = Root /\ s[Len(s)] = n /\
            \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]]
    }

Inv2 ==
    marked \cup frontier = ReachableFromRoot

(* Inv3: Reachable set equality – marked set equals the set of nodes that have a path from Root *)
Inv3 ==
    marked = ReachableFromRoot

(* Partial correctness – when algorithm terminates, all reachable nodes are marked *)
PartialCorrectness ==
    pc = "Done" => marked = ReachableFromRoot

(*-----------------------------------------------------------------
  Liveness property
-----------------------------------------------------------------*)
Termination ==
    <> (pc = "Done")

=============================================================================