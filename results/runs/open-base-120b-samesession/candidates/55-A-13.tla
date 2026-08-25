---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions for the three‑node fully‑meshed graph *)

N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<i, j>> : i \in N1 /\ j \in N1 /\ i # j }
NoNode == "NoNode"

(* Bind the abstract constants to the concrete instances *)

Node == N1
initiator == I1
R == R1

(* Specification used by the model checker *)

TestSpec == Init /\ [][Next]_vars

(* Invariants required by the configuration *)

TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====