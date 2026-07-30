---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    btZenon, btIsabelle, btCVC3, btYices, btVerit, btZ3, btSpass, btLS4,
    btDefaultT, btDefaultM, btDefaultS, btDefaultA

ASSUME /\ btZenon \in STRING
       /\ btIsabelle \in STRING
       /\ btCVC3 \in STRING
       /\ btYices \in STRING
       /\ btVerit \in STRING
       /\ btZ3 \in STRING
       /\ btSpass \in STRING
       /\ btLS4 \in STRING
       /\ btDefaultT \in STRING
       /\ btDefaultM \in STRING
       /\ btDefaultS \in STRING
       /\ btDefaultA \in STRING

SPECIFICATION == Spec
Init == Init
Next == Next
INVARIANTS == Invariants
Properties == Liveness

Extensionality == \A X, Y \in SUBSET (Nat \cup BOOLEAN) : (\A e \in (Nat \cup BOOLEAN) : (e \in X) <=> (e \in Y)) => X = Y
NotAllValues == \A X \in SUBSET (Nat \cup BOOLEAN) : \E e \in (Nat \cup BOOLEAN) : e \notin X

====