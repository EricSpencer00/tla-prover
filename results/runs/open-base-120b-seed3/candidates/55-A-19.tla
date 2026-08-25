---- MODULE MCEcho ----
EXTENDS Naturals, TLC, Echo

CONSTANTS Node, initiator, R, NoNode

(* Basic assumptions required by the Echo algorithm *)
ASSUME NoNode \notin Node
ASSUME initiator \in Node
ASSUME R \subseteq Node \X Node
ASSUME \A <<i, j>> \in R : i # j                     \* irreflexive
ASSUME \A <<i, j>> \in R : <<j, i>> \in R            \* symmetric
ASSUME \A n \in Node : \E m \in Node : <<n, m>> \in R \* connectivity (non‑empty adjacency)

(* Operators that the .cfg file substitutes for the constants *)
N1 == Node
I1 == initiator
R1 == R

(* Reuse the core Echo specification *)
Init == Echo!Init
Next == Echo!Next
vars == Echo!vars

(* Test variant that prints the adjacency relation at start‑up *)
InitPrint == Init /\ Print(R)

TestSpec == InitPrint /\ [][Next]_(vars)

(* Invariants defined in the Echo specification *)
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties

====