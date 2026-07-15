---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* -----------------------------------------------------------------------------
\* Backend pragma operators for the TLA Proof System (TLAPS)
\* These operators are placeholders that are interpreted by the proof system.
\* They do not affect the operational semantics of the specification.
\* -----------------------------------------------------------------------------

\* Dispatch a proof obligation to Zenon with an optional timeout (in seconds)
Zenon(timeout) == TRUE

\* Dispatch a proof obligation to Isabelle with an optional timeout (in seconds)
Isabelle(timeout) == TRUE

\* Dispatch a proof obligation to CVC3 with an optional timeout (in seconds)
CVC3(timeout) == TRUE

\* Dispatch a proof obligation to Yices with an optional timeout (in seconds)
Yices(timeout) == TRUE

\* Dispatch a proof obligation to veriT with an optional timeout (in seconds)
VeriT(timeout) == TRUE

\* Dispatch a proof obligation to Z3 with an optional timeout (in seconds)
Z3(timeout) == TRUE

\* Dispatch a proof obligation to SPASS with an optional timeout (in seconds)
SPASS(timeout) == TRUE

\* Dispatch a proof obligation to the LS4 temporal logic prover with an optional timeout (in seconds)
LS4(timeout) == TRUE

\* -----------------------------------------------------------------------------
\* Temporal logic proof rules (names reserved for future use)
\* The bodies are trivial TRUE propositions; they serve only as identifiers.
\* -----------------------------------------------------------------------------

\* Invariance rule
InvRule(p) == TRUE

\* Strong fairness rule
SFair(p) == TRUE

\* Weak fairness rule
WFair(p) == TRUE

\* Well‑formedness rule
WellFormed(p) == TRUE

\* Step simulation rule
SimStep(p, q) == TRUE

\* -----------------------------------------------------------------------------
\* State variable (there is no real state; the variable is a dummy to give a
\* non‑empty model)
\* -----------------------------------------------------------------------------
VARIABLE x

\* -----------------------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------------------
Init == x = 0

\* -----------------------------------------------------------------------------
\* Next-state relation (does nothing but allow stuttering)
\* -----------------------------------------------------------------------------
Next == x' = x

\* -----------------------------------------------------------------------------
\* Specification (the usual temporal formula)
\* -----------------------------------------------------------------------------
Spec == Init /\ [][Next]_<<x>>

\* -----------------------------------------------------------------------------
\* Safety properties
\* -----------------------------------------------------------------------------

\* Set extensionality: two subsets of the natural numbers that have the same
\* elements are equal.
SetExtensionality ==
  \A A, B \in SUBSET Nat :
    (\A n \in Nat : (n \in A) <=> (n \in B)) => A = B

\* No set contains every possible value (there is no universal set over Nat)
NoUniversalSet ==
  \A S \in SUBSET Nat : \E n \in Nat : n \notin S

\* List of invariants required by the .cfg (empty in this case)
INVARIANT == SetExtensionality /\ NoUniversalSet

\* List of properties required by the .cfg (none)
PROPERTY == TRUE

\* -----------------------------------------------------------------------------
\* Theorem tying everything together
\* -----------------------------------------------------------------------------
THEOREM Spec => []INVARIANT

====