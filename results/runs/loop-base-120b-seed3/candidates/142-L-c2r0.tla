---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS
    Nodes,   \* The set of all graph nodes
    Root,    \* The distinguished start node
    Succ     \* Successor relation: [Nodes -> SUBSET Nodes]

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    marked,   \* Set of nodes already marked as reachable
    frontier, \* Set of nodes whose successors are being explored
    pc        \* Program counter of the sequential algorithm

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
\* The set of nodes reachable from a given set S (the smallest
\* superset of S that is closed under the successor relation).
Reachable(S) ==
    LET
        Closure(T) == T \subseteq Nodes /\ \A n \in T: Succ[n] \subseteq T
    IN
        CHOOSE T \in SUBSET Nodes :
            S \subseteq T /\ Closure(T) /\ 
            \A U \in SUBSET Nodes :
                (S \subseteq U /\ Closure(U)) => T \subseteq U

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "init"

(*-----------------------------------------------------------------
  Next-state relation (placeholder – the real algorithmic actions
  are defined in the extended algorithm module; here we keep the
  definition simple to satisfy the syntactic requirements).
-----------------------------------------------------------------*)
Next ==
    \/ /\ pc = "init"
       /\ pc' = "loop"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "loop"
       /\ UNCHANGED <<marked, frontier, pc>>
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
\* Invariant 1: type correctness and every successor of a marked
\* node is either already marked or in the frontier.
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"init", "loop", "done"}
    /\ \A n \in marked: Succ[n] \subseteq marked \cup frontier

\* Invariant 2: marked ∪ Reachable(frontier) = Reachable(marked ∪ frontier)
Inv2 ==
    marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

\* Invariant 3: Reachable({Root}) = marked ∪ Reachable(frontier)
Inv3 ==
    Reachable({Root}) = marked \cup Reachable(frontier)

INVARIANTS ==
    Inv1 /\ Inv2 /\ Inv3

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Partial‑correctness property
-----------------------------------------------------------------*)
PROPERTIES ==
    (pc = "done") => (marked = Reachable({Root}))

====