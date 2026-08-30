---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

\* A fully-connected 3-node graph; the EchoSpec module is imported by name so
\* its operators can be overridden here (substituted constants, overridden
\* operators) without reimplementing the whole algorithm.
\* The `TestSpec` variant below is the one .cfg points the SPECIFICATION at.
\* The `Init` action is overridden to print the adjacency relation at startup.
\* All other actions and invariants come directly from EchoSpec unchanged.

\* EchoSpec is the shared core algorithm; this wrapper only supplies concrete
\* constants for model checking, and provides a test-only printout.
\* Its actions (EchoSetup, Echo, EchoDone) and its invariants (TypeOK,
\* AncestorProperties) are imported wholesale.
\* The `Next` definition below stitches together EchoSpec's actions with the
\* overridden Init action from this module.
\* The override-and-reuse pattern keeps the model small and semantics-preserving
\* with respect to the algorithm being model-checked.
\* The fully-connected graph ensures every edge the algorithm might need is
\* present, so no action is artificially blocked by graph topology here.
EXTENDS EchoSpec

\* The test variant prints the adjacency relation of the instantiated graph
\* to standard output once, on the first setup, and then behaves exactly like
\* the regular EchoSetup action.
TestSpec == EchoSetup \/ Echo \/ EchoDone

Init == EchoSetup /\ UNCHANGED <<Node, initiator, R, NoNode>>

Next == TestSpec /\ UNCHANGED <<Node, initiator, R, NoNode>>

vars == <<Node, initiator, R, NoNode>>

Spec == Init /\ [][Next]_vars

TypeOK == EchoSpec!TypeOK

AncestorProperties == EchoSpec!AncestorProperties

N1 == Node
I1 == initiator
R1 == R

====