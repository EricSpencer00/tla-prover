---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ------------------------------------------------------------
\* Constants required by the cfg
\* ------------------------------------------------------------
CONSTANTS Nodes, Root, Succ, Seq

\* ------------------------------------------------------------
\* Derived sets
\* ------------------------------------------------------------
Node == Nodes
SeqSet == Seq

\* ------------------------------------------------------------
\* State variables
\* ------------------------------------------------------------
VARIABLES marked, frontier, pc, seqVar

\* ------------------------------------------------------------
\* Helper definitions
\* ------------------------------------------------------------
NoSeq == {}
SeqVal(seq) == seq

\* ------------------------------------------------------------
\* Initial state (inherits the reachability algorithm's init)
\* ------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Init"
  /\ seqVar = {}

\* ------------------------------------------------------------
\* Forward step (inherits the algorithm's forward action)
\* ------------------------------------------------------------
Forward ==
  /\ pc = "Init"
  /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup Succ[n]
        /\ seqVar' = seqVar \cup { n }
        /\ pc' = "Init"

\* ------------------------------------------------------------
\* No-step to allow stuttering when frontier is empty
\* ------------------------------------------------------------
Stutter ==
  /\ frontier = {}
  /\ pc = "Init"
  /\ UNCHANGED <<marked, frontier, seqVar, pc>>

\* ------------------------------------------------------------
\* Next-state relation
\* ------------------------------------------------------------
Next == \/ Forward \/ Stutter

\* ------------------------------------------------------------
\* Specification
\* ------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, seqVar, pc>>

\* ------------------------------------------------------------
\* Invariants
\* ------------------------------------------------------------
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Init"}
  /\ seqVar \in SUBSET SeqSet

Inv1 ==
  /\ frontier = {}
    => marked = Nodes

Inv2 ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes

Inv3 ==
  /\ frontier = {} => marked = Nodes

PartialCorrectness ==
  /\ frontier = {}
    => marked = Nodes

\* ------------------------------------------------------------
\* Termination property (eventually no frontier)
\* ------------------------------------------------------------
Termination == <> (frontier = {})

\* ------------------------------------------------------------
\* THEOREM (optional, for TLC config)
\* ------------------------------------------------------------
THEOREM Spec => []TypeOK

====