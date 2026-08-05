---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences, ParReach

CONSTANT Nodes
CONSTANT Root
CONSTANT Procs
CONSTANT Succ

VARIABLES frontier, marked, pc, sel, succ
vars == <<frontier, marked, pc, sel, succ>>

Init0 == ParReach.Init0
Step == ParReach.Step
Inv == ParReach.Inv
Refines == ParReach.Refines

Init == Init0
Next == Step

SPECIFICATION Spec == Init /\ [][Next]_vars

ConnectedToSomeButAll == Nodes \ {Root}
ConnectedToSomeButNotAll' == Nodes \ {Root}
ConnectedToSomeButNotAll == ConnectedToSomeButAll

FiniteSeq == Seq
FiniteSeq' == Seq
FiniteSeq == FiniteSeq'

====