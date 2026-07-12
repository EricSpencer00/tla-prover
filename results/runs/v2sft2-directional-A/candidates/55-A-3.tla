---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets, Sequences, TLC, "Echo"

CONSTANTS Node, initiator, R, NoNode

(* Concrete instantiation of the required constants *)
Node == {"a", "b", "c"}
initiator == "a"
NoNode == "NoNode"
R == {<<"a","b">>, <<"b","a">>, <<"a","c">>, <<"c","a">>, <<"b","c">>, <<"c","b">>}

(* Safety assumption: the sentinel value is distinct from all nodes *)
NoNode \notin Node

(* The specification of the Echo algorithm (inherited from the Echo module) *)
TestSpec == Echo.Spec

(* The invariants reported by the Echo module *)
TypeOK == Echo.TypeOK
AncestorProperties == Echo.AncestorProperties

====