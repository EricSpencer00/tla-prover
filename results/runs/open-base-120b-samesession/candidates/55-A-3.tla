---- MODULE MCEcho ----
EXTENDS Echo, Naturals, TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions for the three‑node fully‑meshed graph *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {<<x, y>> : x \in N1 /\ y \in N1 /\ x # y}
NoNode == "NoNode"

(* Bind the abstract constants to the concrete definitions *)
Node == N1
initiator == I1
R == R1

(* Specification used by the model checker *)
TestSpec == Init /\ [][Next]_vars

====