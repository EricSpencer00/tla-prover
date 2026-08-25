---- MODULE MCEcho ----
EXTENDS Echo

\*--------------------------------------------------------------------
\* Constants required by the configuration file
\*--------------------------------------------------------------------
CONSTANTS
    Node,
    initiator,
    R,
    NoNode

\*--------------------------------------------------------------------
\* Concrete (finite) definitions that will be substituted for the
\* abstract constants when the model is checked.
\*--------------------------------------------------------------------
N1 == {"n1", "n2", "n3"}                      \* concrete set of nodes
I1 == "n1"                                    \* chosen initiator
R1 == { <<i, j>> : i \in N1 /\ j \in N1 /\ i # j }   \* fully‑meshed, irreflexive, symmetric graph
NoNode == "NoNode"                           \* sentinel value distinct from any node

ASSUME NoNode \notin N1

\*--------------------------------------------------------------------
\* Test specification: the original Echo specification with a
\* side‑effect that prints the adjacency relation at startup.
\* (TLC's Print operator is used for the side‑effect.)
\*--------------------------------------------------------------------
TestSpec ==
    /\ Spec
    /\ TLC!Print("Adjacency relation R1 = " \/ ToString(R1))

====