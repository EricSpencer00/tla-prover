---- MODULE MCEcho ----
EXTENDS Naturals

\* This TLA+ module is the model-checking configuration for the Echo spanning
\* tree algorithm.  It reuses the state, actions, and invariants from Echo.tla
\* (referenced by name) and supplies concrete values for the constants so a
\* model checker can explore the finite reachable state space.

CONSTANTS Node, initiator, R, NoNode

\* The model only redefines the constant declarations from Echo.tla; it does not
\* duplicate the whole Echo specification here.  Every identifier the .cfg
\* file expects to find in this module is provided below, exactly as named.

TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

Init == Echo!Init
Next == Echo!Next
PrintGraph == Echo!PrintGraph

vars == Echo!vars

Spec == Echo!Spec

PrintGraphSpec == Echo!PrintGraphSpec

====