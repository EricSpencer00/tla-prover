---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS zenon, isabelle, cvc3, yices, veriT, z3, spass, ls4, none

ASSUME zenon \in {0, 1}
ASSUME isabelle \in {0, 1}
ASSUME cvc3 \in {0, 1}
ASSUME yices \in {0, 1}
ASSUME veriT \in {0, 1}
ASSUME z3 \in {0, 1}
ASSUME spass \in {0, 1}
ASSUME ls4 \in {0, 1}

Zero == 0

DispatchZenon(v) == IF zenon = 1 THEN Zero ELSE Zero
DispatchIsabelle(v) == IF isabelle = 1 THEN Zero ELSE Zero
DispatchCVC3(v) == IF cvc3 = 1 THEN Zero ELSE Zero
DispatchYices(v) == IF yices = 1 THEN Zero ELSE Zero
DispatchVeriT(v) == IF veriT = 1 THEN Zero ELSE Zero
DispatchZ3(v) == IF z3 = 1 THEN Zero ELSE Zero
DispatchSPASS(v) == IF spass = 1 THEN Zero ELSE Zero
DispatchLS4(v) == IF ls4 = 1 THEN Zero ELSE Zero

Extensionality == \A A, B \in SUBSET {0, 1} : (\A x \in {0, 1} : (x \in A) <=> (x \in B)) => (A = B)
SetNotUniversal == \A X \in SUBSET {0, 1} : X # {0, 1}

SPECIFICATION == Zero
INIT == Zero
NEXT == Zero
INVARIANTS == Zero
PROPERTIES == Extensionality /\ SetNotUniversal
====