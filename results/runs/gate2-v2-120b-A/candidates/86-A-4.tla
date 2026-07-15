---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ****************************************************************************
\* Overview
\* This module provides a configuration infrastructure for the TLA Proof System
\* (TLAPS).  It defines operators that correspond to backend provers (Zenon,
\* Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4) and establishes the fundamental
\* temporal‑logic proof rules described in Lamport's paper “The Temporal Logic
\* of Actions”.  The module also contains two foundational theorems: set
\* extensionality and the existence of a value that is not contained in a given
\* set.
\* ****************************************************************************

\***************************************************************************
\* Backend‑prover operators
\***************************************************************************
Zenon(T)      == @\* dispatch T to the Zenon prover
Isabelle(T)   == @\* dispatch T to the Isabelle prover
CVC3(T)       == @\* dispatch T to the CVC3 prover
Yices(T)      == @\* dispatch T to the Yices prover
VeriT(T)      == @\* dispatch T to the veriT prover
Z3(T)         == @\* dispatch T to the Z3 prover
SPASS(T)      == @\* dispatch T to the SPASS prover
LS4(T)        == @\* dispatch T to the LS4 temporal‑logic prover

\***************************************************************************
\* Temporal‑logic proof rules (names only; no implementation)
\***************************************************************************
\* Invariance rule
InvRule(P)    == @\* placeholder for the invariance proof rule

\* Well‑formedness rules
WFRule(P)    == @\* placeholder for a well‑formedness rule
SFRule(P)    == @\* placeholder for a strong fairness rule
WFRuleWeak(P)== @\* placeholder for a weak fairness rule

\* Step‑simulation rule
StepSim(R)   == @\* placeholder for the step‑simulation rule

\***************************************************************************
\* Foundational theorems
\***************************************************************************
\* Set extensionality: two sets are equal iff they have the same elements.
SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : x \in S <=> x \in T) => S = T

\* No set contains every possible value.
NoSetContainsAll ==
  \A S \in SUBSET UNIV : ~ (\A x : x \in S)

=============================================================================