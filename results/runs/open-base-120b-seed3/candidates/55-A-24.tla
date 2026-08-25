---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC, Echo

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions used to instantiate Echo *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<i, j>> : i \in N1 /\ j \in N1 /\ i # j }

ASSUME NoNode = "NoNode"

(* Instantiate the generic Echo specification with the concrete constants *)
INSTANCE Echo WITH Node <- N1, initiator <- I1, R <- R1, NoNode <- NoNode

(* Print the adjacency relation at the start of the model-checking run *)
PrintR == Print(R1) = R1

(* Specification formula required by the .cfg file *)
TestSpec == Init /\ PrintR /\ [][Next]_vars

====