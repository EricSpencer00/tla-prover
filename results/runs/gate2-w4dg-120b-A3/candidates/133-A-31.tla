---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, BoundedSequences

CONSTANTS Nodes, Root, Procs, Succ

\* The parallel reachability algorithm is defined in the standard library
\* as ReachAlgo (specifically the module that provides Init, Next, Inv,
\* Refines, and the variables it uses).  This configuration module inherits
\* everything it needs from there and adds only the definitions that the
\* model-checking configuration (.cfg) substitutes in place of library
\* operators.
\*   ConnectedToSomeButNotAll replaces Succ in the configuration and is
\*   defined below to be a bounded version of the library's Succ.
\*   LimitedSeq replaces Seq from the Sequences module; it keeps EXTENDS
\*   Sequences so definitions inherited from ReachAlgo keep working while
\*   the model stays finite.

CONSTANTS ConnectedToSomeButNotAll, LimitedSeq

VARIABLES marked, frontier, pc, sel, succ

vars == <<marked, frontier, pc, sel, succ>>

Init == ReachAlgo!Init
Next == ReachAlgo!Next
Spec == ReachAlgo!Spec
Inv == ReachAlgo!Inv
Refines == ReachAlgo!Refines

\* The bounded graph: each node has exactly two successors, taken from the
\* ConnectedToSomeButNotAll operator that the .cfg substitutes for Succ.
ConnectedToSomeButNotAll(x) == Succ(x)

\* The bounded sequence: a FINITE version of Seq so the state space is
\* checkable by model checking.  The .cfg substitutes this for Seq.
LimitedSeq == \E s \in {t \in Seq(Nodes) : Len(t) <= Cardinality(Nodes)} : s

====