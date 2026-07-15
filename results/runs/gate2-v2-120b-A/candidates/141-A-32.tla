---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants required by the .cfg file.
  Nodes   : the set of all graph nodes
  Root    : the distinguished start node (must be in Nodes)
  Succ    : a total function giving, for each node, the set of its
            successor nodes (each successor must also be in Nodes)
  Seq     : a dummy constant required by the configuration; it is
            not used directly in the specification but is kept
            to satisfy the identifier list.
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ, Seq

(*-----------------------------------------------------------------
  State variables
  marked   : the set of nodes that have been visited
  frontier : the set of nodes that are candidates for exploration
  pc       : a program counter that is either "Loop" or "Done"
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Type-correctness predicate required as an invariant.
-----------------------------------------------------------------*)
TypeOK == 
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Loop", "Done"}

(*-----------------------------------------------------------------
  Initial state: no nodes are marked, the frontier contains only the
  root, and the program counter is at the start of the loop.
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Loop"

(*-----------------------------------------------------------------
  Main action (the only nondeterministic step).
  Two cases, chosen nondeterministically from the frontier.
-----------------------------------------------------------------*)
Explore ==
    /\ pc = "Loop"
    /\ frontier # {}
    /\ \E v \in frontier :
        IF v \notin marked THEN
            /\ marked' = marked \cup {v}
            /\ frontier' = frontier \cup Succ[v]
            /\ pc' = "Loop"
        ELSE
            /\ marked' = marked
            /\ frontier' = frontier \ {v}
            /\ pc' = "Loop"

(*-----------------------------------------------------------------
  Termination action: when the frontier is empty the algorithm moves
  to the "Done" state and stays there forever.
-----------------------------------------------------------------*)
Terminate ==
    /\ pc = "Loop"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

(*-----------------------------------------------------------------
  Stuttering step in the terminal state.
-----------------------------------------------------------------*)
Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Next-state relation.
-----------------------------------------------------------------*)
Next == 
    \/ Explore
    \/ Terminate
    \/ Done

(*-----------------------------------------------------------------
  Specification of the algorithm.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Helper definitions for the safety invariants.
-----------------------------------------------------------------*)
MarkedSucc == { y \in Nodes : \E x \in marked : y \in Succ[x] }

Inv1 == 
    /\ MarkedSucc \subseteq marked \cup frontier

Inv2 == 
    /\ (marked \cup frontier) = 
       { x \in Nodes : 
           \E p \in (marked \cup frontier) : x \in ReachFrom(p) }

Inv3 == 
    /\ ReachFrom(Root) = marked \cup ReachFrom(frontier)

(*-----------------------------------------------------------------
  Reachability helper (used in Inv2 and Inv3).  This defines the set of
  nodes reachable from a given set of start nodes by any number of
  Succ steps.
-----------------------------------------------------------------*)
RECURSIVE ReachFrom(_)
ReachFrom(S) ==
    IF S = {} THEN {}
    ELSE S \cup ReachFrom({ y \in Nodes : \E x \in S : y \in Succ[x] })

PartialCorrectness ==
    /\ pc = "Done"
    /\ marked = ReachFrom({Root})

(*-----------------------------------------------------------------
  The list of invariants required by the .cfg file.
-----------------------------------------------------------------*)
InvList == 
    /\ TypeOK
    /\ Inv1
    /\ Inv2
    /\ Inv3
    /\ PartialCorrectness

(*-----------------------------------------------------------------
  Liveness property: eventual termination when the reachable set is
  finite (expressed as a weak fairness assumption on Terminate).
-----------------------------------------------------------------*)
Termination == WF_<<marked, frontier, pc>>(Terminate)

====