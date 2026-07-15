---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

(*---------------------------------------------------------------------------
  Constants
---------------------------------------------------------------------------*)
CONSTANTS
    Nodes,    \* The set of all graph nodes
    Root,     \* The distinguished start node
    Succ,     \* A function mapping each node to the set of its successors
    Seq       \* An arbitrary finite bound used only to give a concrete domain for
              \* the transitive closure operator (not otherwise used directly)

(*---------------------------------------------------------------------------
  Variables
---------------------------------------------------------------------------*)
VARIABLES
    marked,   \* Set of nodes that have been visited
    frontier, \* Set of nodes that are pending exploration (may overlap with marked)
    pc        \* Program counter: "Run" or "Done"

(*---------------------------------------------------------------------------
  Helper definitions
---------------------------------------------------------------------------*)
ReachableFrom(S) ==
    (* The set of nodes reachable from any node in S via zero or more Succ steps *)
    { n \in Nodes : 
        \E path \in Seq: 
            /\ Len(path) >= 1
            /\ path[1] \in S
            /\ \A i \in 1..(Len(path)-1): path[i+1] \in Succ[path[i]]
            /\ path[Len(path)] = n }

(*---------------------------------------------------------------------------
  Initial predicate
---------------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"
    /\ Root \in Nodes

(*---------------------------------------------------------------------------
  Actions
---------------------------------------------------------------------------*)
Explore ==
    /\ pc = "Run"
    /\ frontier # {}
    /\ \E n \in frontier :
        /\ (n \notin marked)
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]      \* n stays in frontier (overlap allowed)
            /\ pc' = "Run"
        \/ (n \in marked)
            /\ marked' = marked
            /\ frontier' = frontier \ {n}
            /\ pc' = "Run"

Terminate ==
    /\ pc = "Run"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Explore
    \/ Terminate

(*---------------------------------------------------------------------------
  Specification
---------------------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>>

(*---------------------------------------------------------------------------
  Safety invariants
---------------------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

Inv1 ==
    \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 ==
    (marked \cup frontier) \cup ReachableFrom(frontier) =
    ReachableFrom(marked \cup frontier)

Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
    /\ pc = "Done"
    /\ marked = ReachableFrom({Root})

(*---------------------------------------------------------------------------
  Liveness property (termination under weak fairness)
---------------------------------------------------------------------------*)
Termination ==
    <> (pc = "Done")

=============================================================================