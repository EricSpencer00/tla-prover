---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root

(*-----------------------------------------------------------------
  Operators from the underlying sequential reachability algorithm.
  They are declared as placeholders here because the description says
  this module extends that algorithm.  In a real development they would
  be imported from another module, but for a self‑contained spec we
  define them minimally.
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc, done

(* Types for readability *)
MarkSet == SUBSET Nodes
FrontierSet == SUBSET Nodes
ProgCtr == {"Init", "Step", "Done"}

(*-----------------------------------------------------------------
  Initial state (INIT)
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Init"
    /\ done = FALSE

(*-----------------------------------------------------------------
  Actions (STEP and TERMINATE)
-----------------------------------------------------------------*)
Step ==
    /\ pc = "Init"
    /\ \/ /\ frontier = {}
          /\ pc' = "Done"
          /\ done' = TRUE
          /\ UNCHANGED <<marked, frontier>>
        \/ \E n \in frontier :
            /\ marked' = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup 
                           { m \in Nodes : m \in Succ(n) /\ 
                                          m \notin marked /\ 
                                          m \notin frontier }
            /\ pc' = "Init"
            /\ UNCHANGED done

Terminate ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc, done>>

Next == Step \/ Terminate

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc, done>>

(*-----------------------------------------------------------------
  Successor relation (graph structure).  This is a placeholder that
  must be constrained by the .cfg file or by additional assumptions.
-----------------------------------------------------------------*)
Succ == [n \in Nodes |-> {}] \* to be overridden by a .cfg constraint

(*-----------------------------------------------------------------
  Invariant 1 (Inductive type correctness and successor condition)
-----------------------------------------------------------------*)
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in ProgCtr
    /\ \A n \in marked :
          \A m \in Nodes :
            (m \in Succ(n)) => (m \in marked \/ m \in frontier)

(*-----------------------------------------------------------------
  Invariant 2 (Reachability decomposition)
-----------------------------------------------------------------*)
(* ReachableFrom(S) = nodes reachable from any node in S using Succ *)
ReachableFrom(S) ==
    RECURSIVE R(_)
    R(S) == S \cup UNION { Succ(n) : n \in S }
    IN R(S)

Inv2 ==
    ReachableFrom(marked) \cup ReachableFrom(frontier) =
    ReachableFrom(marked \cup frontier)

(*-----------------------------------------------------------------
  Invariant 3 (Marked set plus frontier reachability equals full reachable set)
-----------------------------------------------------------------*)
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

(*-----------------------------------------------------------------
  Safety property: partial correctness upon termination
-----------------------------------------------------------------*)
PartialCorrectness ==
    /\ done = TRUE
    /\ marked = ReachableFrom({Root})

(*-----------------------------------------------------------------
  Theorem stating that the specification guarantees the three invariants
  and the partial correctness property.
-----------------------------------------------------------------*)
THEOREM ReachabilityProof ==
    Spec => [](Inv1 /\ Inv2 /\ Inv3) /\ <>PartialCorrectness

(*-----------------------------------------------------------------
  The .cfg file is expected to define the concrete graph (Succ) and
  invoke the model checker with:
    CONSTANTS Nodes = {1,2,3}
    CONSTANTS Root = 1
    INVARIANTS Inv1, Inv2, Inv3
    PROPERTY PartialCorrectness
-----------------------------------------------------------------*)

====