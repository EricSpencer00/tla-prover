---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* Constants (declared in the .cfg)                                         *)
(***************************************************************************)
CONSTANTS
    Nodes,   \* Set of node identifiers
    Root,    \* The distinguished start node
    Succ,    \* Function: Nodes -> SUBSET Nodes (the adjacency relation)
    Seq      \* Upper bound on sequence length (used for path length bound)

(***************************************************************************)
(* Derived sets and functions                                               *)
(***************************************************************************)
Node == Nodes

\* The maximum allowed length for any path (including the empty path)
MaxSeqLen == Seq

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)
VARIABLES
    marked,   \* Set of nodes that have been discovered
    frontier, \* Set of nodes currently being explored
    pc        \* Program counter for the single sequential process

vars == <<marked, frontier, pc>>

(***************************************************************************)
(* Helper definitions                                                      *)
(***************************************************************************)

\* A sequence (list) of nodes is represented as a regular TLA+ sequence.
\* The length is bounded by MaxSeqLen to ensure finiteness.
BoundedSeq == [i \in 0..MaxSeqLen] -> Node

\* The initial state is defined in terms of the inherited algorithm's
\* initialization, specialized to the concrete graph.
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Loop"

\* Successor function: for any node n, Succ[n] gives its set of successors.
\* (Provided as a constant; no definition needed here.)

\* One iteration of the algorithm: pick an element from frontier, move it
\* to marked, add its successors to frontier, and stay in the loop.
Step ==
    /\ pc = "Loop"
    /\ \E n \in frontier :
          /\ marked' = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup Succ[n]
          /\ pc' = "Loop"
    \/ /\ marked = Nodes
          /\ frontier = {}
          /\ pc = "Done"
          /\ UNCHANGED <<marked, frontier, pc>>

Next == Step

\* Temporal specification
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants                                                               *)
(***************************************************************************)

\* Type correctness: all variables stay within their intended domains.
TypeOK ==
    /\ marked \subseteq Node
    /\ frontier \subseteq Node
    /\ pc \in {"Loop", "Done"}

\* Inv1: Successor closure – every node in frontier has a predecessor in marked.
Inv1 ==
    \A n \in frontier :
        \E m \in marked : n \in Succ[m]

\* Inv2: Reachability decomposition – marked and frontier partition the set of nodes reachable from Root.
ReachableFromRoot ==
    { n \in Node :
        \E s \in Seq(0..MaxSeqLen) :
            /\ Len(s) > 0
            /\ s[1] = Root
            /\ s[Len(s)] = n
            /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] }

Inv2 ==
    /\ marked \subseteq ReachableFromRoot
    /\ frontier \subseteq ReachableFromRoot
    /\ marked \cup frontier \subseteq ReachableFromRoot

\* Inv3: Reachable set equality – eventually marked will equal the whole reachable set.
\* As an invariant we assert that marked never exceeds the reachable set.
Inv3 ==
    marked \subseteq ReachableFromRoot

\* PartialCorrectness – when the algorithm terminates, all reachable nodes are marked.
PartialCorrectness ==
    pc = "Done" => marked = ReachableFromRoot

\* Termination – eventually the algorithm reaches the "Done" state.
Termination == <> (pc = "Done")

=============================================================================