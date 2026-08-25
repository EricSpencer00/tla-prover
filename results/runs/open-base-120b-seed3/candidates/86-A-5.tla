---- MODULE TLAPS ----
EXTENDS Naturals, TLC

\*=====================================================================
\* Backend prover dispatch operators (TLAPS pragmas)
\*=====================================================================

\* Each operator represents a directive to TLAPS to use a specific
\* automated prover. The arguments are placeholders for the proof
\* obligation, optional timeout (in seconds), and optional tactics.
\* The bodies are defined as TRUE so that the operators are well‑formed
\* within TLA+, while TLAPS will interpret them according to their names.

Zenon(p, timeout) == TRUE
Isabelle(p, timeout) == TRUE
CVC3(p, timeout) == TRUE
Yices(p, timeout) == TRUE
VeriT(p, timeout) == TRUE
Z3(p, timeout) == TRUE
SPASS(p, timeout) == TRUE
LS4(p, timeout) == TRUE

\*=====================================================================
\* Fundamental theorems about sets
\*=====================================================================

\* Set extensionality: two sets are equal iff they have the same elements.
SetExtensionality ==
  \A S, T : (\A x : (x \in S) \equiv (x \in T)) => S = T

\* There is no universal set (no set contains every possible value).
NoUniversalSet ==
  \A S : ~(\A x : x \in S)

\*=====================================================================
\* Temporal‑logic proof rules (names reserved for future use)
\*=====================================================================

\* Invariance rule
InvarianceRule(p) == TRUE

\* Well‑formedness rule
WellFormednessRule(p) == TRUE

\* Strong fairness rule
StrongFairnessRule(p) == TRUE

\* Weak fairness rule
WeakFairnessRule(p) == TRUE

\* Step‑simulation rule
StepSimulationRule(p) == TRUE

\*=====================================================================
\* Specification skeleton (no state variables)
\*=====================================================================

VARIABLES <<>>   \* No state variables for this configuration module

Init == TRUE

Next == UNCHANGED <<>>

SPECIFICATION == Init /\ [][Next]_<<>>

\* The sets of invariants and temporal properties are empty; the
\* configuration file does not require any.
INVARIANTS == {}

PROPERTIES == {}

====