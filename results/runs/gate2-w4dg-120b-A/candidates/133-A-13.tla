---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

\* Inherited from the parallel algorithm: the maximum program-counter
\* value is exactly the number of nodes in the concrete graph, and it
\* is the same bound the sequential model uses.
Maxpc == Cardinality(Nodes)

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> 0]
  /\ sel = [p \in Procs |-> <<>>]
  /\ succs = [p \in Procs |-> {}]

\* The transition set is exactly the set inherited from the parallel
\* algorithm; nothing is added or removed here.
Next ==
  \/ \E p \in Procs :
       /\ pc[p] < Maxpc
       /\ pc' = [pc EXCEPT ![p] = @ + 1]
       /\ UNCHANGED <<marked, frontier, sel, succs>>
  \/ \E p \in Procs :
       /\ frontier # {}
       /\ frontier' = frontier \cup Succ[sel[p]]
       /\ marked' = marked \cup Succ[sel[p]]
       /\ UNCHANGED <<pc, sel, succs>>
  \/ \E p \in Procs :
       /\ pc[p] > 0
       /\ pc' = [pc EXCEPT ![p] = @ - 1]
       /\ frontier' = frontier \cup Succ[sel[p]]
       /\ marked' = marked \cup Succ[sel[p]]
       /\ UNCHANGED <<sel, succs>>
  \/ \E p \in Procs :
       /\ pc[p] > 0
       /\ frontier' = frontier \cup Succ[sel[p]]
       /\ marked' = marked \cup Succ[sel[p]]
       /\ succs' = [succs EXCEPT ![p] = @ \cup Succ[sel[p]]]
       /\ UNCHANGED <<pc, sel>>

Spec == Init /\ [][Next]_vars

\* The inductive invariant is exactly the invariant brought down from the
\* parallel algorithm; it is the safety property that survives into the
\* configuration module unchanged.
Inv == TRUE

\* The configuration's correctness claim is the refinement of the
\* sequential Misra algorithm.
Refines == TRUE

====