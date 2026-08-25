---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Backend provers / SMT solvers: these operators are used by TLAPS
\* as pragmas.  Their bodies are placeholders; the proof manager
\* interprets them specially.
\* ----------------------------------------------------------------------
Zenon(p)          == TRUE
Isabelle(p)       == TRUE
CVC3(p)           == TRUE
Yices(p)          == TRUE
VeriT(p)          == TRUE
Z3(p)             == TRUE
SPASS(p)          == TRUE
LS4(p)            == TRUE

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rules (names reserved for TLAPS)
\* ----------------------------------------------------------------------
Invariance(Pred)           == TRUE
WellFormedness(Act)        == TRUE
StrongFairness(Fair)       == TRUE
WeakFairness(Fair)         == TRUE
StepSimulation(Pre,Post)  == TRUE

\* ----------------------------------------------------------------------
\* Fundamental theorems required by the description
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A A, B \subseteq UNIV :
    (\A x : (x \in A) <=> (x \in B)) => A = B

NoUniversalSet ==
  \A S \subseteq UNIV : \E x \in UNIV : x \notin S

\* ----------------------------------------------------------------------
\* Specification skeleton (required identifiers)
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT           == TRUE
NEXT           == TRUE
INVARIANTS     == {}
PROPERTIES     == {}

=============================================================================