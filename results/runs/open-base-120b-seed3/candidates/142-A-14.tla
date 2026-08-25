---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, SeqReachability, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
INIT ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "init"
    /\ TypeCorrectness

TypeCorrectness ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"init", "running", "done"}

(* ----------------------------------------------------------------------
   Next-state relation (the sequential Misra reachability algorithm)
   ---------------------------------------------------------------------- *)
NEXT ==
    \/ (* expand a node from the frontier *)
        /\ frontier # {}
        /\ \E n \in frontier :
            /\ marked' = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked')
            /\ pc' = "running"
            /\ UNCHANGED << >>
    \/ (* termination when the frontier is empty *)
        /\ frontier = {}
        /\ pc = "done"
        /\ UNCHANGED <<marked, frontier>>

(* ----------------------------------------------------------------------
   Invariants required for the partial‑correctness proof
   ---------------------------------------------------------------------- *)
Invariant1 ==
    /\ TypeCorrectness
    /\ \A n \in marked :
          \A s \in Succ[n] : s \in marked \/ s \in frontier

Invariant2 ==
    marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

INVARIANTS ==
    /\ Invariant1
    /\ Invariant2
    /\ Invariant3

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec ==
    INIT /\ [][NEXT]_<<marked, frontier, pc>>

(* ----------------------------------------------------------------------
   Partial‑correctness property (the final theorem)
   ---------------------------------------------------------------------- *)
PROPERTIES ==
    Spec => (marked = ReachableFrom({Root}))
====