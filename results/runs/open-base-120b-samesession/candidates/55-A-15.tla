---- MODULE MCEcho ----
EXTENDS Naturals, TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions for the constants, used via the .cfg substitutions *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {<<x, y>> : x \in N1 /\ y \in N1 /\ x # y}
NoNode == "NoNode"

(* Instantiate the generic Echo specification with the concrete values *)
INSTANCE Echo WITH Node <- N1, initiator <- I1, R <- R1, NoNode <- NoNode

(* Specification required by the .cfg file *)
TestSpec == Spec

====