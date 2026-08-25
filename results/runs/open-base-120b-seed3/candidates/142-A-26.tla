---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
  State variables
  - marked  : the set of nodes already marked as reachable
  - frontier: the set of nodes whose successors are being explored
  - pc      : abstract program counter for the sequential algorithm
--------------------------------------------------------------------*)

(*--------------------------------------------------------------------
  Initial state (placeholder – the concrete algorithm supplies the true
  initialization).  We start with the root marked and an empty frontier.
--------------------------------------------------------------------*)
INIT ==
    /\ marked   = {Root}
    /\ frontier = {}
    /\ pc       = "init"

(*--------------------------------------------------------------------
  Next-state relation (placeholder – the real algorithm defines the
  detailed steps).  Here we provide a generic stuttering step and a
  dummy transition that moves the program counter to a terminating
  state.
--------------------------------------------------------------------*)
NEXT ==
    \/ /\ pc = "init"
       /\ pc' = "done"
       /\ UNCHANGED << marked, frontier >>
    \/ /\ pc = "done"
       /\ UNCHANGED << marked, frontier, pc >>

(*--------------------------------------------------------------------
  Graph‑theoretic helpers assumed to be provided by the extended modules:
  - Succ[n]   : the set of immediate successors of node n
  - Reachable(S) : the set of nodes reachable from the set S using Succ
--------------------------------------------------------------------*)

(*--------------------------------------------------------------------
  Invariant 1: type correctness and the successor property.
--------------------------------------------------------------------*)
Inv1 ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked :
          \A s \in Succ[n] : s \in marked \/ s \in frontier

(*--------------------------------------------------------------------
  Invariant 2: reachable nodes from (marked ∪ frontier) equal
              marked ∪ reachable from frontier.
--------------------------------------------------------------------*)
Inv2 ==
    marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

(*--------------------------------------------------------------------
  Invariant 3: reachable nodes from the root equal
              marked ∪ reachable from frontier.
--------------------------------------------------------------------*)
Inv3 ==
    Reachable({Root}) = marked \cup Reachable(frontier)

(*--------------------------------------------------------------------
  Combined invariant operator required by the configuration.
--------------------------------------------------------------------*)
INVARIANTS == Inv1 /\ Inv2 /\ Inv3

(*--------------------------------------------------------------------
  Specification formula required by the configuration.
--------------------------------------------------------------------*)
Spec ==
    INIT /\ [][NEXT]_(<<marked, frontier, pc>>)

(*--------------------------------------------------------------------
  Property (partial‑correctness theorem) required by the configuration.
--------------------------------------------------------------------*)
PROPERTIES == Spec => (marked = Reachable({Root}))

====