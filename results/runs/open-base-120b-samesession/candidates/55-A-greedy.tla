---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions for the three‑node fully‑meshed graph *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>,
        << "n2", "n1" >>,
        << "n1", "n3" >>,
        << "n3", "n1" >>,
        << "n2", "n3" >>,
        << "n3", "n2" >>
      }
NoNode == "NoNode"

(* Bind the constants to the concrete values *)
Node == N1
initiator == I1
R == R1

(* Aliases for invariants defined in Echo, if needed *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

(* Test variant that prints the adjacency relation at start‑up *)
Init == Echo!Init /\ Print(R)
Next == Echo!Next

(* Full specification *)
Spec == Init /\ [][Next]_vars
TestSpec == Spec

====