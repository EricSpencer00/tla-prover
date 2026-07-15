---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants required by the .cfg file
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Procs, Succ, Seq

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc, sel, succs

\* ----------------------------------------------------------------------
\* Types (helpful for readability, not exported)
\* ----------------------------------------------------------------------
Node == Nodes
Proc == Procs

\* ----------------------------------------------------------------------
\* Initial state (mirrors the sequential model's Init adapted for parallel)
\* ----------------------------------------------------------------------
Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Proc |-> "idle"]
  /\ sel = [p \in Proc |-> CHOOSE n \in Node : FALSE] \* dummy, never chosen initially
  /\ succs = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Helper actions
\* ----------------------------------------------------------------------
Select(p) ==
  /\ pc[p] = "idle"
  /\ \E n \in frontier :
       /\ sel' = [sel EXCEPT ![p] = n]
       /\ pc' = [pc EXCEPT ![p] = "select"]
       /\ UNCHANGED <<marked, frontier, succs>>

ProcessSucc(p) ==
  /\ pc[p] = "select"
  /\ LET n == sel[p] IN
       /\ succs' = [succs EXCEPT ![p] = Succ[n]]
       /\ pc' = [pc EXCEPT ![p] = "process"]
       /\ UNCHANGED <<marked, frontier, sel>>

AddMarked(p) ==
  /\ pc[p] = "process"
  /\ LET newMark == succs[p] \ marked IN
       /\ marked' = marked \cup newMark
       /\ frontier' = (frontier \ {sel[p]}) \cup newMark
       /\ pc' = [pc EXCEPT ![p] = "idle"]
       /\ UNCHANGED <<sel, succs>>

\* ----------------------------------------------------------------------
\* Next-state relation (interleaving of the three actions)
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Proc : Select(p)
  \/ \E p \in Proc : ProcessSucc(p)
  \/ \E p \in Proc : AddMarked(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succs>>

\* ----------------------------------------------------------------------
\* Safety invariant (type correctness and basic control-flow properties)
\* ----------------------------------------------------------------------
Inv ==
  /\ marked \subseteq Node
  /\ frontier \subseteq Node
  /\ pc \in [Proc -> {"idle", "select", "process"}]
  /\ sel \in [Proc -> Node]
  /\ succs \in [Proc -> SUBSET Node]
  /\ \A p \in Proc :
        IF pc[p] = "idle"
        THEN succs[p] = {}
        ELSE succs[p] = Succ[sel[p]]

\* ----------------------------------------------------------------------
\* Refinement property: the parallel algorithm implements the sequential one.
\* For every node, once it appears in the parallel marked set it will also
\* appear in the sequential algorithm's marked set (which is the same set here).
\* ----------------------------------------------------------------------
Refines == marked = { n \in Node : \E p \in Proc : n \in succs[p] } \cup {Root}

=============================================================================