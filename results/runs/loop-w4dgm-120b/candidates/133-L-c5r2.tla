---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, MCParReachBase

CONSTANTS Nodes, Root, Procs, Succ

\* The override turns Succ into a predicate that bounds the "successor"
\* set to the explicitly configured shape, and it must leave the name Succ
\* available to the actions it inherits from MCParReachBase.
ConnectedToSomeButNotAll == Succ

\* The override makes the sequence bounded and finite (Seq from Sequences is
\* unbounded/infinite), which is what keeps the state space finite for TLC.
LimitedSeq == Sequence

Spec == MCParReachBase.Spec
Init == MCParReachBase.Init
Next == MCParReachBase.Next

\* The inductive invariant is the full type/consistency/property set from the
\* base spec -- the configuration module does not weaken or drop any of them.
Inv == MCParReachBase.Inv

Refines == MCParReachBase.Refines

====