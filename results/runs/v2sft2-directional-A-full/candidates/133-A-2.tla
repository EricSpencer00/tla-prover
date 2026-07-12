---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

\* ---------- CONSTANTS ----------
CONSTANT Nodes, Root, Procs, Succ, Seq

\* ---------- TYPE DEFINITIONS ----------
Node == Elements(Nodes)

\* ---------- STATE VARIABLES ----------
VARIABLES marked, frontier, pc, selected, succSet

\* ---------- INITIAL STATE ----------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "Init"]
    /\ selected = [p \in Procs |-> <<>>]
    /\ succSet = [p \in Procs |-> <<>>]

\* ---------- NEXT STATE ----------
Next ==
    \/ \E p \in Procs :
          /\ pc[p] = "Init"
          /\ marked' = marked \cup frontier
          /\ frontier' = {}
          /\ pc' = [pc EXCEPT ![p] = "Select"]
          /\ selected' = selected
          /\ succSet' = succSet
    \/ \E p \in Procs :
          /\ pc[p] = "Select"
          /\ selected' = [selected EXCEPT ![p] = Append(selected[p], Head(frontier))]
          /\ frontier' = Tail(frontier)
          /\ pc' = pc
          /\ marked' = marked
          /\ succSet' = succSet
    \/ \E p \in Procs :
          /\ pc[p] = "Select"
          /\ selected[p] \in succSet[p]
          /\ succSet' = [succSet EXCEPT ![p] = Tail(succSet[p])]
          /\ pc' = [pc EXCEPT ![p] = "Send"]
          /\ marked' = marked
          /\ frontier' = frontier
          /\ selected' = selected
    \/ \E p \in Procs :
          /\ pc[p] = "Send"
          /\ frontier' = frontier \cup {Head(succSet[p])}
          /\ pc' = [pc EXCEPT ![p] = "Backtrack"]
          /\ marked' = marked
          /\ succSet' = succSet
          /\ selected' = selected
    \/ \E p \in Procs :
          /\ pc[p] = "Backtrack"
          /\ pc' = [pc EXCEPT ![p] = "Done"]
          /\ marked' = marked
          /\ frontier' = frontier
          /\ succSet' = succSet
          /\ selected' = selected
    \/ \E p \in Procs :
          /\ pc[p] = "Done"
          /\ pc' = [pc EXCEPT ![p] = "Done"]
          /\ UNCHANGED <<marked, frontier, succSet, selected>>

\* ---------- INVARIANT ----------
Inv ==
    /\ TypeOK
    /\ ControlFlowOK

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ frontier = {} \/ Head(frontier) \in Succ[Head(frontier)]
    /\ \A p \in Procs : pc[p] \in {"Init", "Select", "Send", "Backtrack", "Done"}
    /\ \A p \in Procs : selected[p] \in Seq(Nodes)
    /\ \A p \in Procs : succSet[p] \in Seq(Node)

ControlFlowOK ==
    \A p \in Procs :
        (pc[p] = "Send" => selected[p] \in succSet[p])
        /\ (pc[p] = "Backtrack" => AllBacktracks(p))

AllBacktracks(p) ==
    \A prev \in Procs : prev \neq p => pc[prev] \in {"Init", "Done"}

\* ---------- SEQUENTIAL MISRA INVARIANT (as a placeholder) ----------
MisraSeq ==
    /\ marked = Nodes

\* ---------- SPECIFICATION ----------
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc, selected, succSet>>

\* ---------- PROPERTIES ----------
Refines ==
    Spec => []MisraSeq

====