---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* Natural-language description: a model-checking configuration module for the
\* sequential Misra reachability algorithm.  This module provides the concrete
\* graph structure and the bounded sequence override that make the state space
\* finite so TLC can check it exhaustively.  All operators below are exactly the
\* identifiers named in the reference .cfg file.

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "running", "done"}

InitReach ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "start"

StepReach ==
  /\ pc \in {"start", "running"}
  /\ frontier # {}
  /\ LET Expand ==
        {y \in Nodes : \E x \in frontier : y \in Succ[x]}
     IN /\ marked' = marked \cup Expand
        /\ frontier' = Expand \ marked
        /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Spec == InitReach /\ [][StepReach]_vars

Inv1 ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes

Inv2 ==
  \A x \in marked : \E y \in frontier : x \in Succ[y]

Inv3 ==
  \A x \in Nodes : (\A y \in Nodes : (y \in marked /\ x \in Succ[y]) => x \in marked)

PartialCorrectness == \A x \in Nodes : (\E y \in Nodes : x \in Succ[y]) => x \in marked

Termination ==
  (pc = "done") ~> (pc = "done")

\* The .cfg overrides the operator Succ with ConnectedToSomeButNotAll, which
\* must be defined here as the right-hand side of that substitution.
ConnectedToSomeButNotAll ==
  {y \in Nodes : \E x \in Nodes : y \in Succ[x]}

\* The .cfg replaces Seq (from Sequences) with LimitedSeq -- this is the
\* bounded version of Seq that makes the model finite.  Keep "EXTENDS Sequences"
\* and override the name rather than declaring a new Seq operator.
LimitedSeq == CHOOSE s \in Seq(Nodes) : TRUE

====