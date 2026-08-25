---- MODULE TLAPS ----
\* ----------------------------------------------------------------------
\* TLAPS: backend pragmas and temporal‑logic proof‑rule placeholders
\* ----------------------------------------------------------------------
\* This module supplies nullary (or simple) operators that serve as
\* hints to the TLA+ Proof System (TLAPS).  The operators do not affect the
\* semantics of a model; they are only recognised by the proof manager.
\* ----------------------------------------------------------------------

\* ---------------------------- Backend provers ------------------------
\* Each operator can be used as a proof hint, e.g.  BY Zenon.
Zenon(p) == TRUE        \* dispatch to Zenon theorem prover
Isabelle(p) == TRUE     \* dispatch to Isabelle/Isar
CVC3(p) == TRUE         \* dispatch to CVC3 SMT solver
Yices(p) == TRUE        \* dispatch to Yices SMT solver
VeriT(p) == TRUE        \* dispatch to veriT theorem prover
Z3(p) == TRUE           \* dispatch to Z3 SMT solver
SPASS(p) == TRUE        \* dispatch to SPASS prover
LS4(p) == TRUE          \* dispatch to LS4 temporal‑logic prover

\* -------------------------- Temporal‑logic rules --------------------
\* The following operators are placeholders for the standard proof rules
\* from Lamport's *The Temporal Logic of Actions*.  They are defined as
\* constants that always evaluate to TRUE; their names are reserved to
\* avoid clashes with future definitions.

InvariantRule == TRUE            \* invariance rule
WellFormednessRule == TRUE       \* well‑formedness rule
StrongFairnessRule == TRUE       \* strong fairness rule
WeakFairnessRule == TRUE         \* weak fairness rule
StepSimulationRule == TRUE       \* step‑simulation rule

\* ---------------------------- Fundamental theorems ------------------
\* Set extensionality: two sets are equal iff they have the same elements.
SetExtensionality ==
  \A A, B \in SUBSET UNIV :
    (\A x : (x \in A) <=> (x \in B)) => A = B

\* No set contains every possible value (there is no universal set).
NoUniversalSet ==
  ~(\E S : \A x : x \in S)

=============================================================================