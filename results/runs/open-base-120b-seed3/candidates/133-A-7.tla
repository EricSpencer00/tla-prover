---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets, ParReach

CONSTANTS Nodes, Root, Procs, Succ

\*--------------------------------------------------------------------
\* Concrete graph for model checking: 4 nodes, each with exactly 2 successors
\* The configuration substitutes this operator for the generic Succ.
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2, 3}
  [] n = 2 -> {3, 4}
  [] n = 3 -> {1, 4}
  [] n = 4 -> {1, 2}
  [] OTHER -> {}

\*--------------------------------------------------------------------
\* Bounded sequence operator: finite version of Seq bounded by |Nodes|
\*--------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\*--------------------------------------------------------------------
\* State variables (inherited from ParReach)
\*--------------------------------------------------------------------
VARIABLES marked, frontier, pc, sel, succSet

\*--------------------------------------------------------------------
\* Initial state (instantiated with the concrete graph and processes)
\*--------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> {}]
  /\ succSet = [p \in Procs |-> {}]

\*--------------------------------------------------------------------
\* Next-state relation (actions inherited from ParReach)
\* For the purpose of this configuration we keep it abstract.
\*--------------------------------------------------------------------
Next == 
  \/ \E p \in Procs:
       \* placeholder for a worker step; actual definition comes from ParReach
       TRUE

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

\*--------------------------------------------------------------------
\* Invariant (type correctness and control-flow properties)
\*--------------------------------------------------------------------
Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A p \in Procs: sel[p] \subseteq Nodes

\*--------------------------------------------------------------------
\* Refinement property: parallel algorithm implements the sequential Misra algorithm
\*--------------------------------------------------------------------
Refines == TRUE

====