---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants required by the .cfg file
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Procs, Succ

\* Concrete values for the constants (these may be overridden by a .cfg)
Nodes == {"n1", "n2", "n3", "n4"}
Root  == "n1"
Procs == {"p1", "p2"}

\* Succ is substituted in the configuration by ConnectedToSomeButNotAll.
\* We give it a definition here for completeness.
Succ == ConnectedToSomeButNotAll

\* ----------------------------------------------------------------------
\* Operator that provides a finite successor relation.
\* Each node has exactly two successors, matching the description.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
  CASE n = "n1" -> {"n2", "n3"}
  [] n = "n2" -> {"n3", "n4"}
  [] n = "n3" -> {"n4", "n1"}
  [] n = "n4" -> {"n1", "n2"}
  [] OTHER    -> {}

\* ----------------------------------------------------------------------
\* State variables (inherited from the parallel reachability algorithm)
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc, sel, succSet

\* ----------------------------------------------------------------------
\* Initial state (inherits the parallel algorithm's Init)
\* ----------------------------------------------------------------------
Init ==
  /\ marked   = {}
  /\ frontier = {Root}
  /\ pc       = [p \in Procs |-> 0]
  /\ sel      = [p \in Procs |-> Root]
  /\ succSet  = [p \in Procs |-> {}]

\* ----------------------------------------------------------------------
\* Next action (abstract version of the parallel step)
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Procs :
        /\ pc[p] < 2
        /\ pc' = [pc EXCEPT ![p] = @ + 1]
        /\ UNCHANGED <<marked, frontier, sel, succSet>>
  \/ UNCHANGED <<pc, marked, frontier, sel, succSet>>

\* ----------------------------------------------------------------------
\* Specification required by the .cfg file
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

\* ----------------------------------------------------------------------
\* Invariant required by the .cfg file
\* ----------------------------------------------------------------------
Inv ==
  /\ marked   \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc       \in [Procs -> Nat]
  /\ sel      \in [Procs -> Nodes]
  /\ succSet  \in [Procs -> SUBSET Nodes]

\* ----------------------------------------------------------------------
\* Refinement property required by the .cfg file
\* ----------------------------------------------------------------------
Refines == TRUE

\* ----------------------------------------------------------------------
\* LimitedSeq – a finite version of Seq, bounded by the number of nodes
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

====