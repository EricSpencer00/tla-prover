---- MODULE Reachable ----
EXTENDS Naturals, Sequences

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANTS
    Nodes,          \* the set of all graph nodes
    Root,           \* the root node (must be in Nodes)
    Succ            \* successor relation: [Nodes -> SUBSET Nodes]

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES
    marked,         \* set of visited (marked) nodes
    frontier,       \* set of nodes awaiting exploration
    pc              \* program counter: "Run" or "Done"

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
(* the operator that the .cfg substitutes for Succ *)
ConnectedToSomeButNotAll(n) == Succ[n]

(* a finite bound on sequence length, chosen arbitrarily *)
MaxLen == 10

LimitedSeq == { s \in Seq(Nodes) : Len(s) <= MaxLen }

(* reachable nodes from a set S using paths of length ≤ MaxLen *)
REACH(S) ==
    { n \in Nodes :
        \E p \in LimitedSeq :
            /\ Len(p) > 0
            /\ p[1] \in S
            /\ p[Len(p)] = n
            /\ \A i \in 1 .. Len(p)-1 : p[i+1] \in Succ[p[i]] }

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ Root \in Nodes
    /\ Succ \in [Nodes -> SUBSET Nodes]

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
Inv1 == \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 == REACH(marked \cup frontier) = marked \cup REACH(frontier)

Inv3 == REACH({Root}) = marked \cup REACH(frontier)

PartialCorrectness == [](frontier = {} => marked = REACH({Root}))

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ \E n \in frontier :
          /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
          /\ pc' = pc
    \/ \E n \in frontier :
          /\ n \in marked
          /\ marked' = marked
          /\ frontier' = frontier \ {n}
          /\ pc' = pc
    \/ /\ frontier = {}
          /\ pc' = "Done"
          /\ UNCHANGED <<marked, frontier>>

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_<<marked, frontier, pc>>(Next)

(*--------------------------------------------------------------------
  Liveness property
--------------------------------------------------------------------*)
Termination == <> (frontier = {})

=============================================================================