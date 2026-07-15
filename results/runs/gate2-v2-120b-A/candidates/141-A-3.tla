---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(*  Constants (to be supplied in the .cfg file)                             *)
(***************************************************************************)
CONSTANTS
    Nodes,   \* The set of all nodes in the graph
    Root,    \* The distinguished root node (must be in Nodes)
    Succ,    \* A total function mapping each node to the set of its successors
    Seq      \* The set of all simple (acyclic) sequences of nodes

(***************************************************************************)
(*  Derived constants (optional, for readability)                           *)
(***************************************************************************)
\* Ensure that the constants satisfy the basic assumptions
ASSUME Root \in Nodes
ASSUME Succ \in [Nodes -> SUBSET Nodes]

(***************************************************************************)
(*  State variables                                                         *)
(***************************************************************************)
VARIABLES
    visited,    \* Set of nodes that have been marked
    frontier,   \* Set of nodes pending exploration (may overlap visited)
    pc          \* Program counter: either "Loop" or "Done"

(***************************************************************************)
(*  Initial state                                                          *)
(***************************************************************************)
Init ==
    /\ visited = {}
    /\ frontier = {Root}
    /\ pc = "Loop"

(***************************************************************************)
(*  Main action (two nondeterministic cases)                               *)
(***************************************************************************)
Explore ==
    \E n \in frontier :
        IF n \notin visited THEN
            /\ visited' = visited \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ pc' = "Loop"
        ELSE
            /\ visited' = visited
            /\ frontier' = frontier \ {n}
            /\ pc' = "Loop"

(***************************************************************************)
(*  Termination action                                                     *)
(***************************************************************************)
Terminate ==
    /\ frontier = {}
    /\ visited' = visited
    /\ frontier' = frontier
    /\ pc' = "Done"

(***************************************************************************)
(*  Next-state relation                                                     *)
(***************************************************************************)
Next ==
    \/ Explore
    \/ Terminate

(***************************************************************************)
(*  Specification                                                          *)
(***************************************************************************)
Spec ==
    Init /\ [][Next]_<<visited, frontier, pc>>

(***************************************************************************)
(*  Type correctness invariant                                             *)
(***************************************************************************)
TypeOK ==
    /\ visited \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Loop", "Done"}

(***************************************************************************)
(*  Safety invariants                                                       *)
(***************************************************************************)
\* Inv1: Every successor of a visited node is either visited or in the frontier
Inv1 ==
    \A n \in visited : Succ[n] \subseteq visited \cup frontier

\* Inv2: The union of visited and the nodes reachable from frontier equals the
\*       nodes reachable from visited ∪ frontier
Inv2 ==
    Reach(visited \cup frontier) = visited \cup Reach(frontier)

\* Inv3: The nodes reachable from the root equal visited plus nodes reachable
\*       from frontier
Inv3 ==
    Reach({Root}) = visited \cup Reach(frontier)

\* Partial correctness: when terminated, visited equals the reachable set
PartialCorrectness ==
    /\ pc = "Done"
    /\ visited = Reach({Root})

(***************************************************************************)
(*  Reachability helper definitions (finite paths)                         *)
(***************************************************************************)
Reach(S) ==
    UNION { ReachFrom(n) : n \in S }

ReachFrom(n) ==
    { m \in Nodes : <<n, m>> \in Paths }

Paths ==
    { <<n>> : n \in Nodes }                                   \* Paths of length 0
    \cup
    { <<n1, n2, rest>> :
        n1 \in Nodes /\ n2 \in Succ[n1] /\ <<n2, rest>> \in Paths }

(***************************************************************************)
(*  Theorem: Spec implies the listed invariants                              *)
(***************************************************************************)
THEOREM Spec => TypeOK
THEOREM Spec => Inv1
THEOREM Spec => Inv2
THEOREM Spec => Inv3
THEOREM Spec => PartialCorrectness

=============================================================================