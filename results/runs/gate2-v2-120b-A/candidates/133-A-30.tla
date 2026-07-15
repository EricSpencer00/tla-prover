---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*--------------------------------------------------------------------
  Configuration constants (to be instantiated in the .cfg file)
--------------------------------------------------------------------*)
CONSTANT Nodes      \* The set of graph nodes
CONSTANT Root       \* The entry node of the graph
CONSTANT Procs      \* The set of worker processes
CONSTANT Succ       \* Function: Nodes -> Seq(2, Nodes) (2 successors per node)
CONSTANT Seq        \* Upper bound on sequence lengths (>= Cardinality(Nodes))

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
NodeSeq == 0 .. Seq

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    marked,        \* Set of nodes that have been discovered
    frontier,      \* Set of nodes currently being explored
    pc,            \* Per-process program counters
    selected,      \* Per-process selected node (or Null)
    succSet        \* Per-process set of successors awaiting processing

(*--------------------------------------------------------------------
  Type definitions (useful for the type-correctness invariant)
--------------------------------------------------------------------*)
Node == Nodes
Proc == Procs
Null == -1

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ marked    = {Root}
    /\ frontier  = {Root}
    /\ pc        = [p \in Proc |-> "idle"]
    /\ selected  = [p \in Proc |-> Null]
    /\ succSet   = [p \in Proc |-> {}]

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
IsSeq(s) == s \in Seq(NodeSeq)

(*--------------------------------------------------------------------
  Actions (derived from the parallel algorithm; simplified for this model)
--------------------------------------------------------------------*)
Select ==
    /\ \E p \in Proc :
        /\ pc[p] = "idle"
        /\ frontier # {}
        /\ LET n == CHOOSE n \in frontier : TRUE IN
            /\ selected' = [selected EXCEPT ![p] = n]
            /\ frontier' = frontier \ {n}
            /\ pc' = [pc EXCEPT ![p] = "process"]
    /\ UNCHANGED <<marked, succSet>>

Process ==
    /\ \E p \in Proc :
        /\ pc[p] = "process"
        /\ selected[p] # Null
        /\ LET n == selected[p] IN
            /\ succSet' = [succSet EXCEPT ![p] = {Succ[n][1], Succ[n][2]}]
            /\ pc' = [pc EXCEPT ![p] = "add"]
    /\ UNCHANGED <<marked, frontier, selected>>

Add ==
    /\ \E p \in Proc :
        /\ pc[p] = "add"
        /\ succSet[p] # {}
        /\ LET s == CHOOSE x \in succSet[p] : TRUE IN
            /\ succSet' = [succSet EXCEPT ![p] = succSet[p] \ {s}]
            /\ marked' = marked \cup {s}
            /\ frontier' = frontier \cup {s}
            /\ pc' = [pc EXCEPT ![p] = "process"]
    /\ UNCHANGED <<selected, frontier, marked>>

Idle ==
    /\ \E p \in Proc :
        /\ pc[p] = "process"
        /\ selected[p] # Null
        /\ succSet[p] = {}
        /\ pc' = [pc EXCEPT ![p] = "idle"]
        /\ selected' = [selected EXCEPT ![p] = Null]
    /\ UNCHANGED <<marked, frontier, succSet>>

Next ==
    \/ Select
    \/ Process
    \/ Add
    \/ Idle

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc, selected, succSet>>

(*--------------------------------------------------------------------
  Safety invariant (type correctness plus control-flow properties)
--------------------------------------------------------------------*)
Inv ==
    /\ marked \subseteq Node
    /\ frontier \subseteq Node
    /\ pc \in [Proc -> {"idle", "process", "add"}]
    /\ selected \in [Proc -> (Node \cup {Null})]
    /\ succSet \in [Proc -> SUBSET Node]

(*--------------------------------------------------------------------
  Refinement property (placeholder for the actual refinement check)
--------------------------------------------------------------------*)
Refines == Inv

====