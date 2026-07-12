---- MODULE MCEcho ----
EXTENDS TLC, Sequences, FiniteSets, Echo

CONSTANT Node, initiator, R, NoNode

Node          == {"a", "b", "c"}
initiator    == "a"
R            == [n \in Node |-> Node \ {n}]
NoNode       == "None"

(* Inherit the rest of the Echo specification *)
Init          == Echo.Init
Next          == Echo.Next

TestSpec      == Init /\ [][Next]_vars

TypeOK        == Echo.TypeOK
AncestorProperties == Echo.AncestorProperties

====