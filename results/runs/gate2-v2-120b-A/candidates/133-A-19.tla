---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC

\*----------------------------------------------------------------------
\* Constants (to be supplied by the .cfg file)
\*----------------------------------------------------------------------
CONSTANTS Nodes, Root, Procs, Succ, Seq

\*----------------------------------------------------------------------
\* Derived sets
\*----------------------------------------------------------------------
NodeSet == Nodes
ProcSet == Procs

\*----------------------------------------------------------------------
\* Type definitions (optional, used in the invariant)
\*----------------------------------------------------------------------
TypeOK == /\ Marked \in SUBSET NodeSet
          /\ Frontier \in SUBSET NodeSet
          /\ PC \in [ProcSet -> {"Idle", "Select", "Process", "Done"}]
          /\ Select \in [ProcSet -> NodeSet \cup {"None"}]
          /\ SuccSet \in [ProcSet -> SUBSET NodeSet]
          /\ seq \in [ProcSet -> Seq]

\*----------------------------------------------------------------------
\* State variables
\*----------------------------------------------------------------------
VARIABLES Marked, Frontier, PC, Select, SuccSet, seq

\*----------------------------------------------------------------------
\* Helper: sequence override bounded to length |Nodes|
\*----------------------------------------------------------------------
BoundedSeqOverride(s, i, v) ==
  IF i > Len(s) THEN
    s
  ELSE
    Append(SubSeq(s, 1, i - 1), v)

\*----------------------------------------------------------------------
\* Initialization (inherits the sequential init, instantiated with Succ)
\*----------------------------------------------------------------------
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ PC = [p \in ProcSet |-> "Idle"]
  /\ Select = [p \in ProcSet |-> "None"]
  /\ SuccSet = [p \in ProcSet |-> {}]
  /\ seq = [p \in ProcSet |-> <<>>]

\*----------------------------------------------------------------------
\* Actions (parallel algorithm, based on the description)
\*----------------------------------------------------------------------
Idle(p) ==
  /\ PC[p] = "Idle"
  /\ PC' = [PC EXCEPT ![p] = "Select"]
  /\ UNCHANGED <<Marked, Frontier, Select, SuccSet, seq>>

SelectNode(p) ==
  /\ PC[p] = "Select"
  /\ Frontier # {}
  /\ \E n \in Frontier :
        /\ PC' = [PC EXCEPT ![p] = "Process"]
        /\ Select' = [Select EXCEPT ![p] = n]
        /\ SuccSet' = [SuccSet EXCEPT ![p] = Succ[n]]
        /\ seq' = [seq EXCEPT ![p] = Append(seq[p], n)]

ProcessNode(p) ==
  /\ PC[p] = "Process"
  /\ Marked' = Marked \cup {Select[p]}
  /\ Frontier' = (IF Select[p] \in Frontier THEN Frontier \ {Select[p]} ELSE Frontier)
                 \cup (SuccSet[p] \ Marked)
  /\ PC' = [PC EXCEPT ![p] = "Done"]
  /\ UNCHANGED <<Select, SuccSet, seq>>

Done(p) ==
  /\ PC[p] = "Done"
  /\ PC' = [PC EXCEPT ![p] = "Idle"]
  /\ Select' = [Select EXCEPT ![p] = "None"]
  /\ SuccSet' = [SuccSet EXCEPT ![p] = {}]
  /\ UNCHANGED <<Marked, Frontier, seq>>

Next ==
  \/ \E p \in ProcSet : Idle(p)
  \/ \E p \in ProcSet : SelectNode(p)
  \/ \E p \in ProcSet : ProcessNode(p)
  \/ \E p \in ProcSet : Done(p)

\*----------------------------------------------------------------------
\* Specification
\*----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, PC, Select, SuccSet, seq>>

\*----------------------------------------------------------------------
\* Safety invariant (type correctness + control-flow)
\*----------------------------------------------------------------------
Inv == TypeOK

\*----------------------------------------------------------------------
\* Refinement property (placeholder asserting that the parallel algorithm
\* refines the sequential Misra algorithm – details omitted)
\*----------------------------------------------------------------------
Refines == Inv

\*----------------------------------------------------------------------
\* THEOREM (optional, helps TLC)
\*----------------------------------------------------------------------
THEOREM Spec => []Inv

====