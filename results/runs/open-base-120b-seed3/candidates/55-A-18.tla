---- MODULE MCEcho ----
EXTENDS TLC

CONSTANTS Node, initiator, R, NoNode

(* Concrete definitions for the three‑node fully‑meshed graph *)
Node == {"n1", "n2", "n3"}
initiator == "n1"
NoNode == "NoNode"
R == { <<i, j>> : i \in Node /\ j \in Node /\ i # j }

(* Operators used by the .cfg substitution mechanism *)
N1 == Node
I1 == initiator
R1 == R

(* Instantiate the generic Echo specification with the concrete constants *)
INSTANCE Echo AS E WITH Node <- Node,
                     initiator <- initiator,
                     R <- R,
                     NoNode <- NoNode

(* Redefine the initial predicate so that the adjacency relation is printed
   at the start of each model‑checking run.  The equality is trivially true
   and therefore does not affect the behavior of the system. *)
Init == E!Init /\ Print[R] = R

(* The complete specification used by the model checker *)
TestSpec == Init /\ [][E!Next]_(E!Vars)

(* Invariants required by the configuration file *)
TypeOK == E!TypeOK
AncestorProperties == E!AncestorProperties

====