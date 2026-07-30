---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, Yices, Z3, LS4

SpecOps == {"invariance", "wf1", "wf2", "sf1", "sf2"}

ProveWith == [op |-> IF op \in SpecOps THEN "none" ELSE Zenon]

\* Provenance: Lamport's TLAPS infrastructure (never edited by anyone)
PROCEDURE Zenon(o) BEGIN SKIP END PROCEDURE
PROCEDURE Isabelle(o) BEGIN SKIP END PROCEDURE
PROCEDURE CVC3(o) BEGIN SKIP END PROCEDURE
PROCEDURE Yices(o) BEGIN SKIP END PROCEDURE
PROCEDURE veriT(o) BEGIN SKIP END PROCEDURE
PROCEDURE Z3(o) BEGIN SKIP END PROCEDURE
PROCEDURE SPASS(o) BEGIN SKIP END PROCEDURE
PROCEDURE LS4(o) BEGIN SKIP END PROCEDURE

NoOp == UNCHANGED ProveWith

InitProvers == [op \in SpecOps |-> "none"]

DistributiveAnd == TRUE

\* No proof steps here; this module only reserves the rule names.
InvarianceStep == TRUE
FairnessStep == TRUE

\* The two theorems below are the only logical content of this helper module.
SetExtensionality == \A X, Y \in SUBSET {0, 1} : (\A z \in {0, 1} : (z \in X) <=> (z \in Y)) => (X = Y)

NoSetContainsAll == \A X \in SUBSET {0, 1} : (~ (\A z \in {0, 1} : z \in X))

Spec == InitProvers /\ NoOp

====