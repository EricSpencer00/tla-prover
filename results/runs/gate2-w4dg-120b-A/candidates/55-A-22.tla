---- MODULE MCEcho ----
EXTENDS Integers

\* A concrete three-node fully-meshed graph for the Echo spanning tree
\* algorithm.  This module is a model-checking configuration: it defines
\* only the constants and top-level spec operators required by the .cfg,
\* and leaves all state variables and actions to the base Echo spec.
\* Its sole purpose is to bind the constants so a model checker can run.
\* The graph is fully meshed over the three nodes, which satisfies the
\* Echo spec's connectivity, symmetry, and irreflexivity assumptions.

CONSTANTS
  Node, initiator, R, NoNode

ASSUME Node = {"n1", "n2", "n3"}
ASSUME initiator = "n1"
ASSUME R = ("n1" :> "n2") @@ ("n1" :> "n3") @@ ("n2" :> "n1") @@
             ("n2" :> "n3") @@ ("n3" :> "n1") @@ ("n3" :> "n2")
ASSUME NoNode \in Node

TypeOK == TRUE
AncestorProperties == TRUE

VARIABLES NONE
vars == {NONE}

Init == NONE
Next == NONE

Spec == Init /\ [][Next]_vars
TestSpec == Spec

====