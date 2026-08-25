---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions used by the .cfg substitution *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<x, y>> : x \in N1 /\ y \in N1 /\ x # y }

(* sentinel value distinct from all nodes *)
NoNode == "⊥"

(* Test variant that prints the graph adjacency relation at start‑up *)
TestInit == Init /\ Print(R)

TestSpec == TestInit /\ [] [Next]_vars

(* The invariants required by the configuration file are inherited from
   the Echo module; they are therefore already defined. *)
(* TypeOK and AncestorProperties are exported unchanged. *)

====