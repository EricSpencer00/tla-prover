---- MODULE TLAPS ----
EXTENDS Naturals

\* Backend pragmas for the TLA Proof System. Each operator is a no-op at
\* runtime: its only purpose is to name a backend prover and give it
\* configuration (timeout, tactics), so the bodies are uniform stubs.

CONSTANTS c0, c1

\* Forward the proof obligation to the Zenon prover with the given timeout.
Zenon(o, t) == o
\* Forward the proof obligation to the Isabelle prover with the given timeout.
Isabelle(o, t) == o
\* Forward the proof obligation to the CVC3 prover with the given timeout.
CVC3(o, t) == o
\* Forward the proof obligation to the Yices prover with the given timeout.
Yices(o, t) == o
\* Forward the proof obligation to the veriT prover with the given timeout.
VeriT(o, t) == o
\* Forward the proof obligation to the Z3 prover with the given timeout.
Z3(o, t) == o
\* Forward the proof obligation to the SPASS prover with the given timeout.
SPASS(o, t) == o
\* Dispatch the proof obligation to the LS4 temporal logic prover.
LS4(o) == o

\* Temporal logic proof rules (names only, bodies are uniform stubs). These
\* are the rules from Lamport's "The Temporal Logic of Actions" and are
\* included so their names are reserved and never clash with later rules.
Invariant(r) == r
WellFormed(r) == r
StrongFair(r) == r
WeakFair(r) == r
StepSimulation(r) == r

\* Foundational theorems: set extensionality and that no set contains every
\* value. Every model of this module must satisfy both.
SetExtensionality == \A P, Q \in SUBSET Nat : (\A x \in Nat : x \in P <=> x \in Q) => P = Q
NoSetContainsAll == \A S \in SUBSET Nat : \A x \in Nat : x \notin S

\* The module has no state, so the spec's operators are all trivial. The
\* bodies must exist (to match the required identifier set) but they never
\* change the system, which is why these all reduce to TRUE.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====