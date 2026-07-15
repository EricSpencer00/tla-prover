---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants (must be defined in the .cfg file):
    Nodes   - the finite set of node identifiers
    Root    - the distinguished start node, element of Nodes
    Succ    - a function Nodes -> SUBSET Nodes giving successors
    Seq     - a sequence type used to bound paths (not used directly)
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ, Seq

(*-----------------------------------------------------------------
  Derived constant: the set of all possible finite sequences (paths)
  over the nodes, bounded by the number of nodes.  This implements the
  "override for sequences" required by the description.
-----------------------------------------------------------------*)
PathSet == { s \in Seq : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Type definitions (used in the TypeOK invariant)
-----------------------------------------------------------------*)
Node == Nodes
MarkSet == SUBSET Nodes
SeqSet == SUBSET PathSet

(*-----------------------------------------------------------------
  Initial state: only the root is marked and in the frontier,
  program counter is 0 (the first step of the algorithm).
-----------------------------------------------------------------*)
Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = 0

(*-----------------------------------------------------------------
  Next-state relation implements the classic breadth‑first search
  from the underlying reachability algorithm, using the concrete
  graph Succ.  The algorithm proceeds through three PC values:
    0 – normal iteration,
    1 – termination detection,
    2 – final (stuttering) state.
-----------------------------------------------------------------*)
Next ==
    \/ /\ pc = 0
       /\ frontier # {}
       /\ \E n \in frontier :
            /\ marked' = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked')
            /\ pc' = 0
    \/ /\ pc = 0
       /\ frontier = {}
       /\ pc' = 1
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = 1
       /\ pc' = 2
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = 2
       /\ UNCHANGED <<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Specification: the usual temporal formula combining Init and Next.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Invariant: the set of marked nodes is exactly the set of nodes
  reachable from the root via some bounded path.  This ties the state
  variables to the graph Succ.
-----------------------------------------------------------------*)
Inv1 ==
    marked = { n \in Nodes :
                \E s \in PathSet :
                  /\ Len(s) > 0
                  /\ s[1] = Root
                  /\ s[Len(s)] = n
                  /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] }

(*-----------------------------------------------------------------
  Invariant: the frontier is always a subset of the successors of
  the currently marked set, and its elements are unmarked.
-----------------------------------------------------------------*)
Inv2 ==
    /\ frontier \subseteq UNION { Succ[n] : n \in marked }
    /\ frontier \cap marked = {}

(*-----------------------------------------------------------------
  Invariant: no node outside the graph can ever be marked.
-----------------------------------------------------------------*)
Inv3 == marked \subseteq Nodes

(*-----------------------------------------------------------------
  Partial correctness: when the algorithm reaches the final state,
  the marked set contains all nodes reachable from the root.
-----------------------------------------------------------------*)
PartialCorrectness ==
    (pc = 2) => (marked = { n \in Nodes :
                             \E s \in PathSet :
                               /\ Len(s) > 0
                               /\ s[1] = Root
                               /\ s[Len(s)] = n
                               /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] })

(*-----------------------------------------------------------------
  Liveness (termination) property: eventually the algorithm reaches
  the final state (pc = 2) and stays there.
-----------------------------------------------------------------*)
Termination == <> (pc = 2)

(*-----------------------------------------------------------------
  Type correctness invariant required by the configuration.
-----------------------------------------------------------------*)
TypeOK ==
    /\ marked \in MarkSet
    /\ frontier \in MarkSet
    /\ pc \in {0,1,2}
    /\ Nodes \subseteq Nat
    /\ Root \in Nodes
    /\ Succ \in [Nodes -> SUBSET Nodes]

====