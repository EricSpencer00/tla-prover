---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences

\* Configuration module that binds the sequential Misra reachability algorithm
\* to a concrete graph and a bounded sequence override. All identifiers below
\* must match those in the reference TLC configuration.
CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

Init0 ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = 0

Step0 ==
  /\ pc < 2
  /\ pc' = pc + 1
  /\ marked' = marked \cup frontier
  /\ frontier' = {y \in Nodes : \E x \in frontier : y \in Succ[x]}

Done0 ==
  /\ pc = 2
  /\ marked' = marked
  /\ frontier' = frontier
  /\ pc' = pc

Next0 == Step0 \/ Done0

Spec == Init0 /\ [][Next0]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in 0..2

Inv1 == frontier \subseteq Nodes \ frontier \subseteq marked

Inv2 == \A x \in marked : \A y \in Nodes : (y \in Succ[x] => y \in marked)

Inv3 == \A y \in marked : y \in {Root} \cup frontier

PartialCorrectness == marked = Nodes

Termination == <>(pc = 2)

====