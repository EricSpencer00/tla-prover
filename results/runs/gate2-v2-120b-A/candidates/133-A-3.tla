---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC

\* ---------- Constants ----------
CONSTANTS Nodes, Root, Procs, Succ, Seq

\* ---------- Type definitions ----------
Node   == Nodes
Proc   == Procs
NodesSet == SUBSET Node
ProcsSet == SUBSET Proc

\* ---------- State variables ----------
VARIABLES
    marked,          \* shared set of visited nodes
    frontier,        \* shared set of frontier nodes
    pc,              \* program counters for each process
    selected,        \* node selected by each process
    succs,           \* successor set computed by each process
    seqIdx,          \* index into the bounded sequence for each process
    seq               \* per‑process bounded sequence (sequence of nodes)

\* ---------- Helper definitions ----------
Vars == <<marked, frontier, pc, selected, succs, seqIdx, seq>>

\* ---------- Initial state ----------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "Idle"]
    /\ selected = [p \in Procs |-> CHOOSE n \in Node: FALSE]  \* undefined placeholder
    /\ succs = [p \in Procs |-> {}]
    /\ seqIdx = [p \in Procs |-> 0]
    /\ seq = [p \in Procs |-> <<>>]

\* ---------- Actions ----------
Idle(p) ==
    /\ pc[p] = "Idle"
    /\ frontier /= {}
    /\ \E n \in frontier :
          /\ selected' = [selected EXCEPT ![p] = n]
          /\ pc' = [pc EXCEPT ![p] = "Select"]
          /\ UNCHANGED <<marked, frontier, succs, seqIdx, seq>>

Select(p) ==
    /\ pc[p] = "Select"
    /\ seqIdx[p] < Len(Seq)
    /\ succs' = [succs EXCEPT ![p] = Succ[selected[p]]]
    /\ pc' = [pc EXCEPT ![p] = "Process"]
    /\ UNCHANGED <<marked, frontier, selected, seq, seqIdx>>

Process(p) ==
    /\ pc[p] = "Process"
    /\ \E s \in succs[p] :
          /\ marked' = marked \cup {s}
          /\ frontier' = (frontier \cup {s}) \ {selected[p]}
          /\ pc' = [pc EXCEPT ![p] = "Done"]
          /\ UNCHANGED <<selected, succs, seqIdx, seq>>

Done(p) ==
    /\ pc[p] = "Done"
    /\ pc' = [pc EXCEPT ![p] = "Idle"]
    /\ UNCHANGED <<marked, frontier, selected, succs, seqIdx, seq>>

Next ==
    \E p \in Procs:
        \/ Idle(p)
        \/ Select(p)
        \/ Process(p)
        \/ Done(p)

\* ---------- Specification ----------
Spec == Init /\ [][Next]_Vars

\* ---------- Safety invariant ----------
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ marked \cup frontier \subseteq Nodes
    /\ marked \cap frontier = {}
    /\ pc \in [Procs -> {"Idle", "Select", "Process", "Done"}]
    /\ selected \in [Procs -> Node]
    /\ succs \in [Procs -> SUBSET Node]
    /\ \A p \in Procs :
           seqIdx[p] = Len(seq[p])
    /\ \A p \in Procs :
           seq[p] \in Seq

\* ---------- Refinement property ----------
\* The parallel algorithm must implement the sequential Misra algorithm.
\* For illustration we relate it to a set of visited nodes.
Visited ==
    marked

Refines == Visited \subseteq Nodes

====