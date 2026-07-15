---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC, ParReach

CONSTANTS Nodes, Root, Procs, Succ, Seq

Spec == ParReach.Spec
Inv == ParReach.Inv
Refines == ParReach.Refines

====