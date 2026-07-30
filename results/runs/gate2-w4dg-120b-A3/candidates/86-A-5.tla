---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4
CONSTANTS ZenonTimeout, IsabelleTimeout, CVC3Timeout, YicesTimeout
CONSTANTS VeriTTimeout, Z3Timeout

\* Dispatch operators: tell TLAPS which backend prover to use for a given
\* proof obligation. Dispatching never changes system state, it merely
\* records a request and lets the prover carry it out asynchronously.
DispatchZenon == [kind |-> "Zenon", timeout |-> ZenonTimeout]
DispatchIsabelle == [kind |-> "Isabelle", timeout |-> IsabelleTimeout]
DispatchCVC3 == [kind |-> "CVC3", timeout |-> CVC3Timeout]
DispatchYices == [kind |-> "Yices", timeout |-> YicesTimeout]
DispatchVeriT == [kind |-> "VeriT", timeout |-> VeriTTimeout]
DispatchZ3 == [kind |-> "Z3", timeout |-> Z3Timeout]
DispatchSPASS == [kind |-> "SPASS"]
DispatchLS4 == [kind |-> "LS4"]

\* Temporal logic proof rules: these are the building blocks for reasoning
\* about safety and liveness in TLA+. Their bodies are omitted (they are
\* just placeholders reserving the names in the proof library); the
\* actual reasoning is carried out inside TLAPS, not inside the model.
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

\* Foundational theorems: set extensionality and the existence of a value
\* outside any given set.
SetExtensionality == \A A, B \in SUBSET Nat : (\A x \in Nat : x \in A <=> x \in B) => A = B
SomeValueNotInSet == \A A \in SUBSET Nat : \E x \in Nat : x \notin A

\* No operators are left undefined: SPECIFICATION, INIT, NEXT, INVARIANTS,
\* and PROPERTIES all exist, even though they are empty placeholders.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====