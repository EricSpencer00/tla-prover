---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, FiniteSets, TLC, Echo

CONSTANTS Node, initiator, R, NoNode

(* ----------------------------------------------------------------------
   Concrete values used for model checking (substituted via the .cfg file)
   ---------------------------------------------------------------------- *)

N1 == {"n1", "n2", "n3"}                \* the three nodes
I1 == "n1"                               \* deterministic initiator
R1 == {
        <<"n1","n2">>,
        <<"n2","n1">>,
        <<"n1","n3">>,
        <<"n3","n1">>,
        <<"n2","n3">>,
        <<"n3","n2">>
     }                                   \* fully‑meshed undirected graph
NoNode == "NoNode"                       \* sentinel distinct from all nodes

(* ----------------------------------------------------------------------
   Specification and invariants required by the .cfg file
   ---------------------------------------------------------------------- *)

TestSpec == Echo!Spec                     \* the top‑level spec from Echo

TypeOK == Echo!TypeOK                     \* type‑correctness invariant
AncestorProperties == Echo!AncestorProperties
                                          \* spanning‑tree ancestor properties

====