---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

ASSUME Zenon \in Nat /\ Isabelle \in Nat /\ CVC3 \in Nat /\ Yices \in Nat
  /\ veriT \in Nat /\ Z3 \in Nat /\ SPASS \in Nat /\ LS4 \in Nat

\* Theorem system commands: direct an obligation to a specific backend prover
proveWithZenon(q) == q' = "Zenon"
proveWithIsabelle(q) == q' = "Isabelle"
proveWithCVC3(q) == q' = "CVC3"
proveWithYices(q) == q' = "Yices"
proveWithVeriT(q) == q' = "veriT"
proveWithZ3(q) == q' = "Z3"
proveWithSPASS(q) == q' = "SPASS"
proveWithLS4(q) == q' = "LS4"

\* Temporal logic proof rules from Lamport's TLA+, reserved for future versions
invarianceStep(p) == p' = "invariance"
wfStep(f) == p' = "wf(" \o f \o ")"
sfStep(f) == p' = "sf(" \o f \o ")"

\* FACTS: fundamental set-theoretic theorems (not safety properties of a system)
setExtensionality == \A A, B \in SUBSET Nat : (\A x \in Nat : (x \in A) <=> (x \in B)) => (A = B)
noUniversalSet == \A S \in SUBSET Nat : \E x \in Nat : x \notin S

Specification == TRUE
Init == TRUE
Next == TRUE
Invariants == TRUE
Properties == TRUE

====