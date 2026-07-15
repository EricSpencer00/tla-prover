---- MODULE MCParReach ----
EXTENDS ParReach

CONSTANT Nodes = {0, 1, 2, 3}.
CONSTANT Root = 0.
CONSTANT Procs = {1, 2}.
CONSTANT Succ = [0 -> {1, 2}, 1 -> {2, 3}, 2 -> {3, 0}, 3 -> {0, 1}].
CONSTANT Seq = 4.

Spec == ParReach.Spec
Inv == ParReach.Inv
Refines == ParReach.Refines

====