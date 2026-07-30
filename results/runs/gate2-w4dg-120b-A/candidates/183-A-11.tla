---- MODULE TLAPS ----
EXTENDS Integers, FiniteSets

CONSTANTS TLAPlus, Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

VARIABLES prover, timeout, steps

vars == <<prover, timeout, steps>>

Init ==
  /\ prover = TLAPlus
  /\ timeout = 5
  /\ steps = 0

DispatchZenon ==
  /\ prover' = Zenon
  /\ steps' = (steps + 1) % 4
  /\ UNCHANGED timeout

DispatchIsabelle ==
  /\ prover' = Isabelle
  /\ UNCHANGED <<timeout, steps>>

DispatchCVC3 ==
  /\ prover' = CVC3
  /\ UNCHANGED <<timeout, steps>>

DispatchYices ==
  /\ prover' = Yices
  /\ UNCHANGED <<timeout, steps>>

DispatchVeriT ==
  /\ prover' = VeriT
  /\ UNCHANGED <<timeout, steps>>

DispatchZ3 ==
  /\ prover' = Z3
  /\ UNCHANGED <<timeout, steps>>

DispatchSPASS ==
  /\ prover' = SPASS
  /\ UNCHANGED <<timeout, steps>>

DispatchLS4 ==
  /\ prover' = LS4
  /\ UNCHANGED <<timeout, steps>>

SetTimeout(t) ==
  /\ t \in 0..10
  /\ timeout' = t
  /\ UNCHANGED <<prover, steps>>

Next ==
  \/ DispatchZenon \/ DispatchIsabelle \/ DispatchCVC3 \/ DispatchYices
  \/ DispatchVeriT \/ DispatchZ3 \/ DispatchSPASS \/ DispatchLS4
  \/ \E t \in 0..10 : SetTimeout(t)

Spec == Init /\ [][Next]_vars

Extensionality == \A A, B \in SUBSET Nat : (\A x \in Nat : (x \in A) <=> (x \in B)) => (A = B)

NoUniversalSet == \A S \in SUBSET Nat : \E x \in Nat : x \notin S

Invariance == TRUE
WFWellFormed == TRUE
StrongFairness == TRUE
WeakFairness == TRUE
StepSimulation == TRUE
====