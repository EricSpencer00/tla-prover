---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC, Echo

\*--------------------------------------------------------------------
\* Concrete values for the model‑checking instance
\*--------------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
     }
\* Sentinel value for “no parent”.  It must be distinct from every node.
NoNode == "NoNode"

\* Bind the abstract constants to the concrete values for the MC run.
ASSUME Node = N1
ASSUME initiator = I1
ASSUME R = R1
ASSUME NoNode = NoNode

\*--------------------------------------------------------------------
\* Re‑export the core components of the Echo algorithm.
\* (Echo provides Init, Next, Spec, TypeOK and AncestorProperties.)
\*--------------------------------------------------------------------
Init == Echo!Init
Next == Echo!Next

\* The specification that the .cfg file refers to.
TestSpec == Echo!Spec

\* Invariants required by the .cfg file.
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====