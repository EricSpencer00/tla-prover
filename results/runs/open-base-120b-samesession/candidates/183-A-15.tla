---- MODULE TLAPS ----
EXTENDS TLC

\* ----------------------------------------------------------------------
\* Backend provers (names reserved for TLAPS configuration)
\* ----------------------------------------------------------------------
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rule names (reserved identifiers)
\* ----------------------------------------------------------------------
CONSTANTS Invariance, WellFormed, StrongFairness, WeakFairness, StepSimulation

\* ----------------------------------------------------------------------
\* Fundamental theorems required by the library
\* ----------------------------------------------------------------------
\* Set extensionality: two sets are equal iff they have the same elements.
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

\* No set contains every possible value (there is no universal set).
THEOREM NoUniversalSet ==
  \A S : S # UNIV

====