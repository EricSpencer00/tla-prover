---- MODULE MCEcho ----
EXTENDS TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete values for the three‑node fully‑meshed graph *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<x, y>> : x \in N1 /\ y \in N1 /\ x # y }
NoNode == "NoNode"

(* Instantiate the generic Echo specification with the concrete constants *)
INSTANCE Echo AS EchoInst WITH
    Node <- N1,
    initiator <- I1,
    R <- R1,
    NoNode <- NoNode

(* Specification and invariants required by the .cfg file *)
TestSpec == EchoInst!Spec

TypeOK == EchoInst!TypeOK
AncestorProperties == EchoInst!AncestorProperties

====