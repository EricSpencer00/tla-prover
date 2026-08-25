---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R

(* Concrete definitions for the three‑node fully‑meshed graph *)
ASSUME Node = {"n1", "n2", "n3"}
ASSUME initiator = "n1"
ASSUME R = {<<x, y>> : x \in Node /\ y \in Node /\ x # y}
ASSUME NoNode \notin Node

(* Operators used by the .cfg substitution *)
N1 == Node
I1 == initiator
R1 == R

(* Specification alias for the test configuration *)
TestSpec == Spec

====