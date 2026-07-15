---------------- MODULE MCReachable ----------------
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  This module configures the sequential Misra reachability algorithm
  for model checking over a concrete graph with 4 nodes, each
  having exactly two successors.  It also introduces a bounded
  sequence type to keep the state space finite.
-----------------------------------------------------------------*)

CONSTANTS
    Nodes,   \* The set of node identifiers (e.g., {1,2,3,4})
    Root,    \* The distinguished start node
    Succ,    \* Function giving the set of successors of each node
    Seq      \* The set of finite sequences over Nodes (bounded length)

(*-----------------------------------------------------------------
  State variables: marked set, frontier set, and program counter.
-----------------------------------------------------------------*)
VARIABLES
    marked,   \* Set of nodes that have been discovered
    frontier, \* Set of nodes currently being explored
    pc        \* Control location: "Init", "Loop", or "Done"

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
SeqBound == Cardinality(Nodes)  \* Upper bound on sequence length

Seq == { s \in Seq(Nodes) : Len(s) <= SeqBound }

(*-----------------------------------------------------------------
  Initial state (inherits from the algorithm specification)
-----------------------------------------------------------------*)
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc        = "Loop"

(*-----------------------------------------------------------------
  Algorithm actions (inherited from the sequential reachability
  algorithm).  The actions are written directly here for completeness.
-----------------------------------------------------------------*)
Explore ==
    /\ pc = "Loop"
    /\ frontier # {}               \* There is at least one node to explore
    /\ \E n \in frontier :
          /\ marked'   = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked')
    /\ pc' = "Loop"

Terminate ==
    /\ pc = "Loop"
    /\ frontier = {}
    /\ marked' = marked
    /\ frontier' = frontier
    /\ pc' = "Done"

Next ==
    \/ Explore
    \/ Terminate

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK ==
    /\ marked   \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc       \in {"Init", "Loop", "Done"}

(* Inv1: Successor closure – every node in frontier has a predecessor in marked or is the root *)
Inv1 ==
    \A n \in frontier :
        n = Root \/ \E m \in marked : n \in Succ[m]

(* Inv2: Reachability decomposition – marked is exactly the set of nodes reachable from Root via a bounded sequence *)
Inv2 ==
    marked = { n \in Nodes :
                \E s \in Seq :
                    /\ Len(s) >= 1
                    /\ s[1] = Root
                    /\ s[Len(s)] = n
                    /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] }

(* Inv3: Reachable set equality – the set of nodes reachable from Root equals marked *)
Inv3 ==
    { n \in Nodes :
        \E s \in Seq :
            /\ Len(s) >= 1
            /\ s[1] = Root
            /\ s[Len(s)] = n
            /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] }
    = marked

(* PartialCorrectness – when the algorithm terminates, marked contains all nodes reachable from Root *)
PartialCorrectness ==
    pc = "Done" => Inv2

(*-----------------------------------------------------------------
  Liveness property: termination
-----------------------------------------------------------------*)
Termination ==
    <> (pc = "Done")

=============================================================================