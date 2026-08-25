---- MODULE MCEcho ----
EXTENDS TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete three‑node fully‑meshed graph *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<i, j>> : i \in N1 /\ j \in N1 /\ i # j }
NoNode == "NoNode"

(* Instantiate the generic Echo specification with the concrete constants *)
INSTANCE Echo AS E WITH
    Node      <- N1,
    initiator <- I1,
    R         <- R1,
    NoNode    <- NoNode

(* Add a print of the adjacency relation at startup *)
Init == E!Init /\ Print(R1)
Next == E!Next

(* The top‑level specification to be checked *)
TestSpec == E!Spec

(* Invariants required by the configuration *)
TypeOK == E!TypeOK
AncestorProperties == E!AncestorProperties
====