---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-----------------------------------------------------------------
  Configuration constants (to be instantiated by the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root, Procs, Succ, Seq

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
Node   == Nodes
Proc   == Procs

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Succs(p) == Succ[p]

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    marked,          \* Set of nodes that have been marked as reachable
    frontier,        \* Set of nodes currently in the frontier
    pc,              \* Program counter for each process (control state)
    selected,        \* Node selected by each process from its frontier
    succSet,         \* Set of successors of the selected node for each process
    seq              \* Bounded sequence used for the override operation

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = [p \in Proc |-> "idle"]
    /\ selected = [p \in Proc |-> NULL]
    /\ succSet = [p \in Proc |-> {}]
    /\ seq = <<>>

(*-----------------------------------------------------------------
  Actions (per-process)
-----------------------------------------------------------------*)
Select(p) ==
    /\ pc[p] = "idle"
    /\ frontier # {}
    /\ \E n \in frontier :
          /\ selected' = [selected EXCEPT ![p] = n]
          /\ pc' = [pc EXCEPT ![p] = "selected"]
          /\ UNCHANGED <<marked, frontier, succSet, seq>>

AcquireSucc(p) ==
    /\ pc[p] = "selected"
    /\ selected[p] # NULL
    /\ succSet' = [succSet EXCEPT ![p] = Succs(selected[p])]
    /\ pc' = [pc EXCEPT ![p] = "process_succ"]
    /\ UNCHANGED <<marked, frontier, selected, seq>>

Mark(p) ==
    /\ pc[p] = "process_succ"
    /\ succSet[p] # {}
    /\ \E n \in succSet[p] :
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup {n}
          /\ succSet' = [succSet EXCEPT ![p] = succSet[p] \ {n}]
          /\ pc' = [pc EXCEPT ![p] = "process_succ"]
          /\ UNCHANGED <<selected, seq>>
    \/ (succSet[p] = {} /\ pc' = [pc EXCEPT ![p] = "idle"]
        /\ UNCHANGED <<marked, frontier, selected, succSet, seq>>)

OverrideSeq ==
    /\ pc = [p \in Proc |-> "idle"]
    /\ Len(seq) < Cardinality(Nodes)
    /\ seq' = Append(seq, {n \in Nodes : n # seq[Len(seq)]})
    /\ UNCHANGED <<marked, frontier, pc, selected, succSet>>

Done ==
    /\ frontier = {}
    /\ pc = [p \in Proc |-> "idle"]
    /\ UNCHANGED <<marked, frontier, selected, succSet, seq>>

Next ==
    \/ \E p \in Proc : Select(p)
    \/ \E p \in Proc : AcquireSucc(p)
    \/ \E p \in Proc : Mark(p)
    \/ OverrideSeq
    \/ Done

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc, selected, succSet, seq>>

(*-----------------------------------------------------------------
  Invariant (type correctness + control-flow properties)
-----------------------------------------------------------------*)
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Proc -> {"idle", "selected", "process_succ"}]
    /\ selected \in [Proc -> (Nodes \cup {NULL})]
    /\ succSet \in [Proc -> SUBSET Nodes]
    /\ Len(seq) <= Cardinality(Nodes)
    /\ \A p \in Proc :
          /\ pc[p] = "idle" => selected[p] = NULL
          /\ pc[p] = "selected" => selected[p] \in frontier
          /\ pc[p] = "process_succ" => succSet[p] = Succs(selected[p])

(*-----------------------------------------------------------------
  Refinement property (parallel algorithm refines sequential Misra)
-----------------------------------------------------------------*)
Refines == Spec /\ Inv

=============================================================================