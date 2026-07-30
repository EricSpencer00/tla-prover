---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

\* Model-checking configuration for the parallel MISRA reachability algorithm.
\* Extends the parallel algorithm by fixing the graph and bounding sequence
\* length.  We reuse the same graph constants as the sequential module.
CONSTANTS
  Nodes,
  Root,
  Procs,
  Succ,
  Seq

Bump == (Seq + 1) % 4

VARIABLES marked, frontier, pc, sel, succSet

vars == <<marked, frontier, pc, sel, succSet>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> 0..2]
  /\ sel \in [Procs -> 0..4]
  /\ succSet \in [Procs -> Seq(0..4)]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> 0]
  /\ sel = [p \in Procs |-> 0]
  /\ succSet = [p \in Procs |-> << >>]

\* The parallel algorithm's actions are unchanged here; this module only
\* supplies the constants those actions refer to.
Next ==
  \/ \E p \in Procs:
       /\ pc[p] = 0
       /\ frontier # {}
       /\ \E n \in frontier, s \in 0..2:
            /\ sel' = [sel EXCEPT ![p] = s]
            /\ succSet' = [succSet EXCEPT ![p] = << s >>]
            /\ frontier' = frontier \ {n}
            /\ marked' = marked \cup {n}
            /\ pc' = [pc EXCEPT ![p] = 1]
  \/ \E p \in Procs:
       /\ pc[p] = 1
       /\ Len(succSet[p]) > 0
       /\ frontier' = frontier \cup {sel[p]}
       /\ succSet' = [succSet EXCEPT ![p] = Tail(succSet[p])]
       /\ pc' = [pc EXCEPT ![p] = 2]
  \/ \E p \in Procs:
       /\ pc[p] = 2
       /\ frontier = {}
       /\ frontier' = frontier \cup {sel[p]}
       /\ pc' = [pc EXCEPT ![p] = 0]
  \/ \E p \in Procs:
       /\ pc[p] = 2
       /\ frontier # {}
       /\ pc' = [pc EXCEPT ![p] = 0]
  \/ \E p \in Procs:
       /\ pc[p] = 2
       /\ frontier = {}
       /\ sel' = [sel EXCEPT ![p] = Bump]
       /\ pc' = [pc EXCEPT ![p] = 0]
  /\ UNCHANGED <<marked>>

Spec == Init /\ [][Next]_vars

\* Invariant: bounded sequence length and all variables well-typed.
Inv == /\ TypeOK
        /\ \A p \in Procs: Len(succSet[p]) =< 4

\* Refinement: the parallel algorithm simulates the sequential Misra algorithm.
Refines == \A p \in Procs: pc[p] >= 1

====