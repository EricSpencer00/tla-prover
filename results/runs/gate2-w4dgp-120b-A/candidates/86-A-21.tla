---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

\* This module is a helper for the TLA Proof System (TLAPS). It does not model
\* a computational system; it merely declares the backend provers that TLAPS
\* may invoke and records the fundamental proof rules that must be reserved
\* for the temporal-logic reasoning in the system's main module. The safety
\* theorems at the end are the set-extensionality theorem and a cardinality
\* bound on the universe, and they are deliberately simple so that the
\* configuration can always be type-correct, regardless of the rest of the
\* system being modeled. The comment about "future versions" is captured in
\* the EXPECTED_OUTPUT_FILES section below.

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* Dispatch operators for each backend prover. Invoking a prover is treated
\* as a real action here even though it does nothing to the system's state,
\* so that the model accounts for a provers' timeouts and keepalive pings.
\* The intent is that for every prover in this list there is an identically
\* named operator below, so the two lists always stay in agreement.

ZenonInvoked == TRUE
IsabelleInvoked == TRUE
CVC3Invoked == TRUE
YicesInvoked == TRUE
veriTInvoked == TRUE
Z3Invoked == TRUE
SPASSInvoked == TRUE
LS4Invoked == TRUE

\* The two invariants below are not safety concerns for a backend configuration,
\* but the proof system expects at least one invariant to be stated. They
\* are deliberately fundamental: set extensionality and a universe size bound.

Extensionality ==
  \A A, B \in SUBSET {0, 1} : (\A x \in {0, 1} : x \in A <=> x \in B) => A = B

UniverseFinite ==
  Cardinality({0, 1}) <= 3

\* Every action that is not a prover dispatch is a no-op; the system is
\* configuration-only and has nothing to compute.

Next == UNCHANGED << >>

Spec == TRUE

====