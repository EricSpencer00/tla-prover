---- MODULE MCEcho ----
EXTENDS FiniteSets, Sequences, TLC

CONSTANTS Node, initiator, R, NoNode

(*-----------------------------------------------------------------
   Concrete instantiation for model checking
  -----------------------------------------------------------------*)
N1 == {"n1", "n2", "n3"}               \* concrete set of nodes
I1 == "n1"                             \* deterministic initiator
R1 == { << "n1", "n2" >>,
        << "n2", "n1" >>,
        << "n1", "n3" >>,
        << "n3", "n1" >>,
        << "n2", "n3" >>,
        << "n3", "n2" >> }           \* fully‑meshed undirected graph

(* NoNode must be distinct from every element of N1 *)
ASSUME NoNode # "n1" /\ NoNode # "n2" /\ NoNode # "n3"

(*-----------------------------------------------------------------
   Import the generic Echo specification
  -----------------------------------------------------------------*)
INSTANCE Echo WITH
    Node   <- Node,
    initiator <- initiator,
    R      <- R,
    NoNode <- NoNode

(*-----------------------------------------------------------------
   Specification, initialization, next‑state, and invariants
  -----------------------------------------------------------------*)
vars == Echo!vars

Init == Echo!Init

Next == Echo!Next

TestSpec == Init /\ [][Next]_vars

TypeOK == Echo!TypeOK

AncestorProperties == Echo!AncestorProperties

====