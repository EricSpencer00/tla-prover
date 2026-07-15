---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* This module defines backend pragmas for TLAPS and re‑states two
\* foundational theorems from set theory.
\* ----------------------------------------------------------------------

\* ---------- Backend pragma operators ----------
\* Each operator simply returns the arguments unchanged; in a real
\* configuration these would be interpreted by TLAPS to select a prover.
\* The names are reserved for TLAPS backend dispatch.

Zenon(ts) == ts
Isabelle(ts) == ts
CVC3(ts) == ts
Yices(ts) == ts
VeriT(ts) == ts
Z3(ts) == ts
SPASS(ts) == ts
LS4(ts) == ts

\* ---------- Temporal‑logic proof‑rule operators ----------
\* These operators are placeholders for the temporal‑logic rules
\* described in Lamport’s “The Temporal Logic of Actions”.  They do not
\* change state; they merely expose the rule names so that TLAPS can
\* reference them.

Invariance(rule) == rule
WellFormedness(rule) == rule
StrongFairness(rule) == rule
WeakFairness(rule) == rule
StepSimulation(rule) == rule

\* ---------- Fundamental set‑theoretic theorems ----------
\* Both theorems are expressed as operators that evaluate to a Boolean.
\* They are included so the model checker can verify them trivially.

SetExtensionality == 
  \A A, B \in SUBSET UNIV : (\A x \in UNIV : x \in A <=> x \in B) => A = B

NoUniversalSet == 
  \A A \in UNIV : \E x \in UNIV : x \notin A

\* ---------- Dummy state to satisfy TLC ----------
\* The specification does not model any concrete state, but TLC
\* requires at least one variable and an Init/Next pair.
VARIABLE dummy

Init == dummy = 0

Next == dummy' = (dummy + 1) % 2

\* ---------- Specification components ----------
SPECIFICATION == Init /\ [][Next]_<<dummy>>
INIT         == Init
NEXT         == Next
INVARIANTS   == SetExtensionality
PROPERTIES   == NoUniversalSet

=============================================================================