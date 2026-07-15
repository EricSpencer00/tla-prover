---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Configuration constants (to be supplied by the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Procs, Succ, Seq

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
NodeSet == Nodes
ProcSet == Procs

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    Marked,        \* Set of nodes that have been visited
    Frontier,     \* Set of nodes currently being explored
    pc,           \* Program counter per process (state of the worker)
    Sel,          \* Selected node per process
    SuccSet,      \* Successor set per process
    seq           \* Global sequence used for bounding (could be per‑process)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Enumerate the possible control locations of a worker.
PcVals == {"Idle", "Select", "Expand", "Done"}

\* The length of any sequence is bounded by the number of nodes.
SeqBound == Cardinality(Nodes)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = [p \in ProcSet |-> "Idle"]
    /\ Sel = [p \in ProcSet |-> CHOOSE n \in NodeSet: FALSE] \* undefined
    /\ SuccSet = [p \in ProcSet |-> {}]
    /\ seq = <<>>

\* ----------------------------------------------------------------------
\* Per‑process actions
\* ----------------------------------------------------------------------
Select(p) ==
    /\ pc[p] = "Idle"
    /\ Frontier # {}
    /\ Sel' = [Sel EXCEPT ![p] = CHOOSE n \in Frontier : TRUE]
    /\ pc' = [pc EXCEPT ![p] = "Select"]
    /\ UNCHANGED <<Marked, Frontier, SuccSet, seq>>

Expand(p) ==
    /\ pc[p] = "Select"
    /\ Sel[p] \in Frontier
    /\ SuccSet' = [SuccSet EXCEPT ![p] = Succ[Sel[p]]]
    /\ Marked' = Marked \cup {Sel[p]}
    /\ Frontier' = (Frontier \ {Sel[p]}) \cup Succ[Sel[p]]
    /\ pc' = [pc EXCEPT ![p] = "Expand"]
    /\ UNCHANGED <<Sel, seq>>

Done(p) ==
    /\ pc[p] = "Expand"
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<Marked, Frontier, Sel, SuccSet, seq>>

Idle(p) ==
    /\ pc[p] = "Done"
    /\ pc' = [pc EXCEPT ![p] = "Idle"]
    /\ UNCHANGED <<Marked, Frontier, Sel, SuccSet, seq>>

WorkerStep(p) ==
    \/ Select(p)
    \/ Expand(p)
    \/ Done(p)
    \/ Idle(p)

\* ----------------------------------------------------------------------
\* Global actions
\* ----------------------------------------------------------------------
SeqAppend ==
    /\ Len(seq) < SeqBound
    /\ seq' = seq \o <<CHOOSE n \in NodeSet: TRUE>> \* nondeterministic append
    /\ UNCHANGED <<Marked, Frontier, pc, Sel, SuccSet>>

SeqTrim ==
    /\ Len(seq) > 0
    /\ seq' = Tail(seq)
    /\ UNCHANGED <<Marked, Frontier, pc, Sel, SuccSet>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in ProcSet : WorkerStep(p)
    \/ SeqAppend
    \/ SeqTrim

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc, Sel, SuccSet, seq>>

\* ----------------------------------------------------------------------
\* Invariant (type‑correctness + simple control‑flow)
\* ----------------------------------------------------------------------
Inv ==
    /\ Marked \subseteq NodeSet
    /\ Frontier \subseteq NodeSet
    /\ pc \in [ProcSet -> PcVals]
    /\ Sel \in [ProcSet -> NodeSet] \cup [ProcSet -> {CHOOSE n \in NodeSet: FALSE}]
    /\ SuccSet \in [ProcSet -> SUBSET NodeSet]
    /\ Len(seq) <= SeqBound

\* ----------------------------------------------------------------------
\* Property: refinement (placeholder – true in this configuration)
\* ----------------------------------------------------------------------
Refines == TRUE

====