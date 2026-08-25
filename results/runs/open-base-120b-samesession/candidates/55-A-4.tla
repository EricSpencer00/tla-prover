---- MODULE MCEcho ----
EXTENDS Echo, TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete concrete definitions for the three‑node fully‑meshed graph.
   The configuration file can map the constants Node, initiator, and R
   to these operators. *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<i, j>> : i \in N1 /\ j \in N1 /\ i # j }

(* A sentinel value that is guaranteed not to be a node. *)
NoNode == "NoNode"

(* Side‑effect that prints the adjacency relation when the spec
   is initialized; the Print function is provided by TLC. *)
PrintR == Print(R)

(* Specification used by the model checker. *)
TestSpec == Init /\ PrintR /\ [][Next]_vars

(* Invariants required by the .cfg file; they are defined in the
   Echo module and are simply re‑exported here. *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====