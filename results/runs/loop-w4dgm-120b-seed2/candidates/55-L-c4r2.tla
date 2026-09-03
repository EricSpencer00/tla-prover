---- MODULE MCEcho ----
EXTENDS Naturals, Echo

\* This TLA+ module is the model-checking configuration for the Echo spanning
\* tree algorithm.  It reuses the state, actions, and invariants from Echo.tla
\* and supplies concrete values for the constants so a model checker can explore
\* the finite reachable state space.  It also defines the identifiers the .cfg
\* file expects to find in this module.

CONSTANTS Node, initiator, R, NoNode

\* The model only redefines the constant declarations from Echo.tla; it does not
\* duplicate the whole Echo specification here.  Every identifier the .cfg
\* file expects to find in this module is provided below.

TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

Init == Echo!Init
Next == Echo!Next
PrintGraph == Echo!PrintGraph

vars == Echo!vars

Spec == Echo!Spec

PrintGraphSpec == Echo!PrintGraphSpec

\* The .cfg file substitutes small finite values for the constants, so the test
\* spec is the configuration-instantiated version of the full Echo spec.
TestSpec == Echo!Spec

N1 == Node
I1 == initiator
R1 == R

====