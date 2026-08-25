---- MODULE MCEcho ----
EXTENDS Echo, FiniteSets, Sequences

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions for substitution by the .cfg file *)
N1 == {"A", "B", "C"}
I1 == "A"
R1 == {<<i, j>> : i \in Node /\ j \in Node /\ i # j}
NoNode == "None"

(* Consistency assumption: the sentinel is distinct from all nodes *)
ASSUME NoNode \notin Node

(* Bind the abstract constants to the concrete definitions *)
Node == N1
initiator == I1
R == R1

(* Specification that the model checker will explore *)
TestSpec == Spec

(* The invariants are defined in the extended Echo module *)
(* They are exposed here under the required names *)
(*   TypeOK          – type correctness invariant *)
(*   AncestorProperties – spanning‑tree ancestor properties invariant *)

====