---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Backend pragma operators for TLAPS (no operational effect in the model)
\* ----------------------------------------------------------------------
Zenon(p) == p
Isabelle(p) == p
CVC3(p) == p
Yices(p) == p
VeriT(p) == p
Z3(p) == p
SPASS(p) == p
LS4(p) == p

\* ----------------------------------------------------------------------
\* Temporal logic proof rule placeholders (no operational effect)
\* ----------------------------------------------------------------------
InvRule(P) == P
WFRule(P) == P
SFRule(P) == P
StepSim(P) == P

\* ----------------------------------------------------------------------
\* State variable (the only variable needed to give the module a concrete
\* state for TLC; its concrete meaning is irrelevant for the proof‑rule
\* placeholders)
\* ----------------------------------------------------------------------
VARIABLE x

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init == x = 0

\* ----------------------------------------------------------------------
\* Next-state relation (trivial, keeps the variable unchanged)
\* ----------------------------------------------------------------------
Next == x' = x

\* ----------------------------------------------------------------------
\* Specification (standard temporal operator)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<x>>

\* ----------------------------------------------------------------------
\* Safety theorems required by the description
\* ----------------------------------------------------------------------
SetExtensionality == \A S, T \in SUBSET Nat : (\A y \in Nat : (y \in S) = (y \in T)) => S = T

NoSetContainsAll == \A S \in SUBSET Nat : \E y \in Nat : y \notin S

\* ----------------------------------------------------------------------
\* The module does not declare any additional constants, invariants,
\* or properties because the .cfg file does not require any.
\* ----------------------------------------------------------------------
=============================================================================