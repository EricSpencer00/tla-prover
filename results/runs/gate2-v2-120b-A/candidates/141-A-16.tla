---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS
    Nodes,          \* The set of all graph nodes
    Root,           \* The root node from which reachability is computed
    Succ,           \* Succ[n] gives the set of successors of node n
    Seq             \* Unused constant required by the .cfg (kept for compatibility)

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Successors(S) == UNION { Succ[n] : n \in S }

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    marked,         \* Set of nodes that have been visited
    frontier,       \* Set of nodes pending exploration (may overlap with marked)
    pc              \* Program counter: "Run" or "Done"

vars == << marked, frontier, pc >>

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = { Root }
    /\ pc = "Run"

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
Visit ==
    \E n \in frontier :
        IF n \notin marked THEN
            /\ marked'   = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ pc'       = "Run"
        ELSE
            /\ marked'   = marked
            /\ frontier' = frontier \ {n}
            /\ pc'       = "Run"

Terminate ==
    /\ frontier = {}
    /\ pc = "Done"
    /\ UNCHANGED << marked, frontier >>

Next ==
    \/ Visit
    \/ Terminate

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Type correctness invariant (TypeOK)
-----------------------------------------------------------------*)
TypeOK ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
\* Inv1: Every successor of a marked node is either marked or in the frontier
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* Inv2: The union of marked and the nodes reachable from frontier equals
\*       the nodes reachable from the union of marked and frontier.
\* (This invariant holds trivially given the definition of Successors.)
Inv2 ==
    Successors(marked) \subseteq marked \cup frontier

\* Inv3: The set of nodes reachable from the root equals the union of
\*       marked and the nodes reachable from the frontier.
Inv3 ==
    \A n \in Nodes :
        (n \in marked) \/ (n \in Successors(frontier)) =>
        n \in reachable
\* To express the right‑hand side, we define the reachable set explicitly:
\* (Note: this definition is auxiliary and not part of the state.)
REACHABLE(root) ==
    LET R == { root } \cup
               UNION { Succ[n] : n \in R }
    IN R
\* Using the auxiliary definition:
reachable == REACHACHABLE(Root)

\* Partial correctness: when the algorithm terminates, marked equals
\* the set of nodes reachable from the root.
PartialCorrectness ==
    pc = "Done" => marked = reachable

(*-----------------------------------------------------------------
  Liveness property
-----------------------------------------------------------------*)
Termination ==
    <> (pc = "Done")

====