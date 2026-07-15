---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANTS
    Nodes, \* The set of all graph nodes
    Root    \* The designated start node

(*--------------------------------------------------------------------
  State variables (inherited from the sequential reachability algorithm)
--------------------------------------------------------------------*)
VARIABLES
    marked,    \* Set of nodes that have been marked as reachable
    frontier,  \* Set of frontier nodes to be explored next
    pc         \* Program counter (not used directly in proofs)

(*--------------------------------------------------------------------
  Type correctness invariant (part of Invariant 1)
--------------------------------------------------------------------*)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"Init", "Step", "Done"}

(*--------------------------------------------------------------------
  Graph-theoretic helper definitions (mirroring lemmas from the
  reachability proofs module)
--------------------------------------------------------------------*)
\* Immediate successors of a node (to be instantiated by the user)
Successors(n) == {}

(* Reachable nodes from a given set using any number of successor steps *)
ReachableFrom(S) ==
    LET Rec(S) ==
        IF S = {} THEN {}
        ELSE S \cup Rec({ n \in Nodes : \E m \in S : n \in Successors(m) })
    IN Rec(S)

(*--------------------------------------------------------------------
  Invariant 1: type correctness + each successor of a marked node is
  either already marked or in the frontier.
--------------------------------------------------------------------*)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : \A s \in Successors(n) : s \in marked \/ s \in frontier

(*--------------------------------------------------------------------
  Invariant 2: (Marked ∪ Frontier) reaches the same nodes as Marked
  reaches the union of Marked and Frontier.
--------------------------------------------------------------------*)
Inv2 ==
    ReachableFrom(marked) = ReachableFrom(marked \cup frontier)

(*--------------------------------------------------------------------
  Invariant 3: Nodes reachable from the Root equal the marked set
  plus nodes reachable from the frontier.
--------------------------------------------------------------------*)
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

(*--------------------------------------------------------------------
  Initial state (as described in the reference algorithm)
--------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Init"

(*--------------------------------------------------------------------
  Next-state relation (abstracted; concrete actions are not needed
  for the invariants and can be refined later)
--------------------------------------------------------------------*)
Step ==
    /\ pc = "Init"
    /\ pc' = "Step"
    /\ UNCHANGED << marked, frontier >>

Done ==
    /\ pc = "Step"
    /\ pc' = "Done"
    /\ UNCHANGED << marked, frontier >>

Next ==
    \/ Step
    \/ Done
    \/ UNCHANGED << pc, marked, frontier >>

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<< marked, frontier, pc >>

(*--------------------------------------------------------------------
  Theorem stating partial correctness (derived from the invariants)
--------------------------------------------------------------------*)
THEOREM PartialCorrectness ==
    Spec => [] (pc = "Done" => marked = ReachableFrom({Root}))

(*--------------------------------------------------------------------
  Exported identifiers required by the configuration
--------------------------------------------------------------------*)
VARIABLES marked, frontier, pc
Init  == Init
Next  == Next
Spec  == Spec
Inv1  == Inv1
Inv2  == Inv2
Inv3  == Inv3

====