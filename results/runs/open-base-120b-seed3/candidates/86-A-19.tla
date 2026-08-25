---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Backend pragma identifiers for TLAPS.  They are defined as simple
\* constants whose values are the names of the external provers; the
\* proof system interprets them specially.
\* ----------------------------------------------------------------------
Zenon   == "zenon"
Isabelle == "isabelle"
CVC3    == "cvc3"
Yices   == "yices"
veriT   == "verit"
Z3      == "z3"
SPASS   == "spass"
LS4     == "ls4"

\* ----------------------------------------------------------------------
\* Temporal‑logic proof‑rule names (place‑holders).  Their definitions are
\* irrelevant for model checking; they merely reserve the identifiers.
\* ----------------------------------------------------------------------
InvarianceRule      == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule   == TRUE
StepSimulationRule == TRUE

\* ----------------------------------------------------------------------
\* Foundational theorems required by the description.
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) \iff (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : ~ (UNIV \subseteq S)

====