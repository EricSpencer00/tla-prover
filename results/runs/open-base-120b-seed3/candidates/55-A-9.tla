---- MODULE MCEcho ----
EXTENDS Echo, TLC

\* ----------------------------------------------------------------------
\* Concrete constants (will be instantiated by the cfg via substitution)
\* ----------------------------------------------------------------------
CONSTANT Node, initiator, R, NoNode

\* ----------------------------------------------------------------------
\* Finite concrete values used for substitution in the configuration file
\* ----------------------------------------------------------------------
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        <<"n1","n2">>, <<"n1","n3">>,
        <<"n2","n1">>, <<"n2","n3">>,
        <<"n3","n1">>, <<"n3","n2">>
      }
NoNode == "NoNode"

\* ----------------------------------------------------------------------
\* Bind the model‑checking constants to the concrete values
\* ----------------------------------------------------------------------
Node == N1
initiator == I1
R == R1

\* ----------------------------------------------------------------------
\* Export the invariants defined in the Echo specification
\* ----------------------------------------------------------------------
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

\* ----------------------------------------------------------------------
\* Aliases for the actions defined in Echo
\* ----------------------------------------------------------------------
Init == Echo!Init
Next == Echo!Next

\* ----------------------------------------------------------------------
\* The specification used by the model checker.
\* It prints the adjacency relation at the start of each run.
\* ----------------------------------------------------------------------
TestSpec == Echo!Spec /\ Print(R)

\* ----------------------------------------------------------------------
\* Names required by the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION == TestSpec
INVARIANTS == { TypeOK, AncestorProperties }
PROPERTIES == {}

====