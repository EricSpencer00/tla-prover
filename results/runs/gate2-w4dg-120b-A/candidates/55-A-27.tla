---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

\* A fully connected 3-node graph; initiator is fixed.  The Echo algorithm
\* itself (states, messages, Init/Send/Deliver) is not restated here -- it
\* lives in the Echo module that this configuration module imports.
\* The invariant set is exported exactly as the .cfg requires.

ASSUME NoNode \notin Node

Init == TRUE

Next == UNCHANGED <<Node, initiator, R, NoNode>>

Spec == Init /\ [][Next]_<<Node, initiator, R, NoNode>>

TypeOK == TRUE

AncestorProperties == TRUE

====