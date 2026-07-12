---- MODULE MCEcho ----
EXTENDS Echo

CONSTANT Node, initiator, R, NoNode

(* Concrete instantiation for exhaustive model checking *)
Node      == {"A", "B", "C"}
initiator == "A"
R         == { [a, b] : a \in Node /\ b \in Node /\ a # b }
NoNode    == "None"

(* Ensure the sentinel is distinct from all nodes *)
NoNode \notin Node

\* Specification: alias the specification defined in the Echo module
TestSpec == Spec

\* Invariant aliases as required by the .cfg
INVARIANT TypeOK, AncestorProperties

====