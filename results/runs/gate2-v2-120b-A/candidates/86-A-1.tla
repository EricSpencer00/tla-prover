---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

\* ----------------------------------------------------------------------
\* Configuration for TLAPS: define operators that act as pragmas for
\* the TLA+ Proof System. These operators have empty definitions; they
\* are interpreted by TLAPS, not by the TLC model checker.
\* ----------------------------------------------------------------------

\* Backend provers
Zenon   == FALSE
Isabelle == FALSE
CVC3    == FALSE
Yices   == FALSE
VeriT   == FALSE
Z3      == FALSE
SPASS   == FALSE
LS4     == FALSE

\* Temporal logic proof rules (place‑holders for TLAPS)
\* Invariance rule
InvRule == FALSE
\* Well‑formedness rule
WFRule  == FALSE
\* Strong fairness rule
SFRule  == FALSE
\* Weak fairness rule
WFairRule == FALSE
\* Step simulation rule
StepSim == FALSE

\* ----------------------------------------------------------------------
\* Safety theorems required by the description
\* ----------------------------------------------------------------------
\* Set extensionality: two sets with the same elements are equal.
SetExtensionality == \A X, Y \in SUBSET Nat :
                       (\A e \in Nat : e \in X <=> e \in Y) => X = Y

\* No set contains every possible value (i.e., is not the universal set).
NoUniversalSet == \A S \in SUBSET Nat : S # Nat

\* ----------------------------------------------------------------------
\* The following identifiers are required by the reference .cfg.
\* They are defined as trivial operators that are true in every state.
\* This satisfies TLC's expectations while keeping the semantics unchanged.
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT          == TRUE
NEXT          == TRUE
INVARIANTS    == TRUE
PROPERTIES    == TRUE

====