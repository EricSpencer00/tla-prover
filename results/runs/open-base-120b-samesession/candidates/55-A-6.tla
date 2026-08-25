---- MODULE MCEcho ----
EXTENDS Echo

CONSTANT Node, initiator, R, NoNode

(* Concrete definitions used by the model checker *)

N1 == {"A", "B", "C"}               \* the three nodes
I1 == "A"                           \* the deterministic initiator
R1 == { << "A", "B" >>, << "B", "A" >>,
        << "A", "C" >>, << "C", "A" >>,
        << "B", "C" >>, << "C", "B" >> }   \* fully‑meshed undirected graph

NoNode == "NoNode"                  \* a distinguished value not in N1

(* Specification and invariants required by the .cfg file *)

TestSpec == Spec

TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====