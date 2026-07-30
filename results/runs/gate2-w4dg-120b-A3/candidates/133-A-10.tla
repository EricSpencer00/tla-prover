---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

(* This is a model-checking configuration module for the parallel reachability  *)
(* algorithm.  It inherits all of the algorithm's state, actions, and specs, and  *)
(* adds only the concrete configuration: a specific graph and a bounded sequence *)
(* override that makes the model finite.                                        *)

CONSTANTS Nodes, Root, Procs, Succ

\* Succ is overridden by the .cfg to ConnectedToSomeButNotAll; ConnectedToSomeButNotAll
\* is defined here as a specific finite graph where each node has exactly two
\* successors, keeping the finite-state model checking tractable.
ConnectedToSomeButNotAll(x) ==
  CASE x = 1 : {2, 3}
  [] x = 2 : {3, 4}
  [] x = 3 : {1, 4}
  [] x = 4 : {1, 2}

\* Seq is overridden by the .cfg to LimitedSeq, a FINITE version of Sequences.
LimitedSeq(S) == SelectSeq(S, 4)

\* The parallel algorithm's module is included here; it defines the state vars,   *
\* the Init, NextSpec, Inv, and Refines operators (the algorithm's spec), and  *
\* expects Succ and Seq to be supplied by the configuration module.
INCLUDE ParallelAlgoSpec

Spec == Init /\ [][NextSpec]_<<Marked, Frontier, PC, Sel, SuccSet>>

====