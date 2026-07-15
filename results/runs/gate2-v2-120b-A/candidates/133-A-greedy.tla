---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants required by the .cfg file
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root, Procs, Succ, Seq

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Node == Nodes
Proc == Procs

(*-----------------------------------------------------------------
  State variables (inherited from the parallel algorithm)
-----------------------------------------------------------------*)
VARIABLES
    marked,        \* Set of nodes that have been discovered
    frontier,      \* Set of nodes currently being explored
    pc,            \* Program counter per process (control state)
    sel,           \* Selected node per process (or NULL)
    succs          \* Successor set per process (subset of Node)

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
NULL == -1

ProcStates == {"Idle", "Select", "Explore", "Done"}

(*-----------------------------------------------------------------
  Initial state (inherits from the parallel algorithm)
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Proc |-> "Idle"]
    /\ sel = [p \in Proc |-> NULL]
    /\ succs = [p \in Proc |-> {}]

(*-----------------------------------------------------------------
  Actions (inherited from the parallel algorithm)
-----------------------------------------------------------------*)
Select(p) ==
    /\ pc[p] = "Idle"
    /\ frontier # {}
    /\ sel[p] \in frontier
    /\ pc' = [pc EXCEPT ![p] = "Explore"]
    /\ succs' = [succs EXCEPT ![p] = Succ[sel[p]]]
    /\ UNCHANGED <<marked, frontier, sel>>

Explore(p) ==
    /\ pc[p] = "Explore"
    /\ marked' = marked \cup {sel[p]}
    /\ frontier' = (frontier \ {sel[p]}) \cup succs[p]
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<sel, succs>>

Done(p) ==
    /\ pc[p] = "Done"
    /\ pc' = [pc EXCEPT ![p] = "Idle"]
    /\ UNCHANGED <<marked, frontier, sel, succs>>

Next ==
    \/ \E p \in Proc : Select(p)
    \/ \E p \in Proc : Explore(p)
    \/ \E p \in Proc : Done(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succs>>

(*-----------------------------------------------------------------
  Safety invariant (type correctness + control-flow properties)
-----------------------------------------------------------------*)
Inv ==
    /\ marked \subseteq Node
    /\ frontier \subseteq Node
    /\ pc \in [Proc -> ProcStates]
    /\ sel \in [Proc -> (Node \cup {NULL})]
    /\ succs \in [Proc -> SUBSET Node]
    /\ \A p \in Proc :
          (pc[p] = "Idle" => sel[p] = NULL)
          /\ (pc[p] = "Explore" => sel[p] \in Node)
          /\ (pc[p] = "Done" => sel[p] \in Node)

(*-----------------------------------------------------------------
  Refinement property: parallel algorithm implements the sequential Misra algorithm.
  For illustration, we assert that the set of marked nodes is always a subset of the
  nodes reachable from the root via the Succ relation, which is a key property of the
  sequential algorithm.
-----------------------------------------------------------------*)
ReachableFromRoot ==
    RECURSIVE Reach(_)
    Reach(n) ==
        IF n = Root THEN {Root}
        ELSE {n} \cup UNION { Reach(m) : m \in Succ[n] }

Refines ==
    marked \subseteq ReachableFromRoot

====