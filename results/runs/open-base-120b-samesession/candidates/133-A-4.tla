---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* ----------------------------------------------------------------------
\*  Concrete graph definition used for model checking.
\*  Each node has exactly two successors.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
  { (n % Cardinality(Nodes)) + 1,
    ((n + 1) % Cardinality(Nodes)) + 1 }

\* ----------------------------------------------------------------------
\*  Bounded version of Seq, needed because the .cfg replaces Seq with this
\* ----------------------------------------------------------------------
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\*  State variables (inherited from the parallel reachability algorithm)
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc, sel, succSet

\* ----------------------------------------------------------------------
\*  Initial state (concrete instantiation)
\* ----------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> {}]
  /\ succSet = [p \in Procs |-> {}]

\* ----------------------------------------------------------------------
\*  Next-state relation (abstract version of the parallel algorithm)
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Procs :
        /\ pc[p] = "idle"
        /\ \E n \in frontier :
              /\ sel' = [sel EXCEPT ![p] = {n}]
              /\ frontier' = frontier \ {n}
              /\ marked' = marked \cup {n}
              /\ pc' = [pc EXCEPT ![p] = "busy"]
              /\ UNCHANGED << succSet >>
  \/ \E p \in Procs :
        /\ pc[p] = "busy"
        /\ LET s == ConnectedToSomeButNotAll(Select(sel[p]))
           IN /\ frontier' = frontier \cup s
              /\ pc' = [pc EXCEPT ![p] = "idle"]
              /\ UNCHANGED << marked, sel, succSet >>
  \/ UNCHANGED << marked, frontier, pc, sel, succSet >>

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

\* ----------------------------------------------------------------------
\*  Invariant (type correctness + simple control‑flow properties)
\* ----------------------------------------------------------------------
Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "busy"}]
  /\ sel \in [Procs -> SUBSET Nodes]
  /\ succSet \in [Procs -> SUBSET Nodes]

\* ----------------------------------------------------------------------
\*  Refinement property (placeholder for the actual refinement statement)
\* ----------------------------------------------------------------------
Refines == Inv

====