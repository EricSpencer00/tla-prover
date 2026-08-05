---- MODULE MCReachable ----
EXTENDS Integers, Sequences

\* Model-checking configuration for the sequential Misra reachability algorithm.
\* This module defines concrete graph constants and a bounded sequence type so
\* that the exhaustive state space stays finite for TLC.
CONSTANTS Nodes, Root, Succ

VARIABLES marked, fringe, pc
vars == <<marked, fringe, pc>>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ fringe \in SUBSET Nodes
  /\ pc \in {"idle", "searching", "done"}

Init ==
  /\ marked = {Root}
  /\ fringe = Succ[Root]
  /\ pc = "searching"

ExploreStep(n) ==
  /\ n \in fringe
  /\ n \notin marked
  /\ fringe' = (fringe \cup Succ[n]) \ {n}
  /\ marked' = marked \cup {n}
  /\ UNCHANGED pc

Step == \E n \in Nodes : ExploreStep(n)

Complete ==
  /\ pc = "searching"
  /\ fringe = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, fringe>>

Next ==
  \/ Step
  \/ Complete

Spec == Init /\ [][Next]_vars

\* Invariants carried over from the standard algorithm.
Inv1 ==
  \A n \in fringe : \E m \in marked : n \in Succ[m]

Inv2 ==
  \A n \in marked : \E s \in Seq(Nodes) :
    /\ Head(s) = Root
    /\ \A i \in DOMAIN s : n \in Succ[s[i]]
    /\ \A i \in DOMAIN s : s[i] \in Nodes

Inv3 ==
  marked \subseteq {n \in Nodes : \E s \in Seq(Nodes) :
                      /\ Head(s) = Root
                      /\ \A i \in DOMAIN s : n \in Succ[s[i]]
                      /\ \A i \in DOMAIN s : s[i] \in Nodes}

PartialCorrectness ==
  \A n \in Nodes : (n \in marked) => (n \in {Root} \cup fringe)

Termination == <>(pc = "done")

====