---- MODULE MCEcho ----
EXTENDS Sequences, FiniteSets, TLC, Echo

CONSTANTS Node, initiator, R, NoNode

(* 
   The Echo module provides the variables, Init, Next, TypeOK, and AncestorProperties.
   This module simply instantiates the Echo specification with the concrete constants
   specified in the .cfg.  The TestSpec operator is required by the configuration.
*)

Spec == Init /\ [][Next]_vars

TestSpec == Spec

INVARIANTS TypeOK, AncestorProperties

====