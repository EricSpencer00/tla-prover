---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS noProv, noSat, noSmt, noSim, noStep

\* Backend pragmas for TLAPS: which prover to dispatch a subgoal to, plus its
\* timeout or tactic.
Zenon(x)   == noProv
Isabelle(x) == noProv
CVC3(x)    == noSat
Yices(x)   == noSat
VeriT(x)   == noSat
Z3(x)      == noSat
SPASS(x)   == noSat
LS4(x)     == noSmt

\* Temporal-logic proof rules (from Lamport's TLA+ book). These are the
\* foundations of the logic and are never derived; they are reserved so future
\* modules cannot silently re-use their names.
InvRule(P)    == noSim
WFRule(P)     == noSim
SFRule(P)     == noSim
StepRule(t)   == noStep

\* Foundational theorems that the module asserts as always holding.
SETEXTENSIONALITY == noSat
NODIAGONAL == noSat

Spec == noSat
Init == noSat
Next == noSat
Invariants == noSat
Properties == noSat

====