---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions used for substitution by the .cfg file *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<x, y>> : x \in N1 /\ y \in N1 /\ x # y }

(* Bind the abstract constants to the concrete definitions *)
ASSUME Node = N1
ASSUME initiator = I1
ASSUME R = R1
ASSUME NoNode = "None"

(* Specification to be checked by TLC *)
TestSpec == Init /\ [][Next]_vars

(* The invariants TypeOK and AncestorProperties are inherited from Echo *)

====