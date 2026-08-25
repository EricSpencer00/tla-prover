---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Backend prover dispatch operators (pragmas).  They simply return the
\* argument they are given; their purpose is to reserve the names for
\* TLAPS configuration.
\* ----------------------------------------------------------------------
Zenon(p) == p
Isabelle(p) == p
CVC3(p) == p
Yices(p) == p
VeriT(p) == p
Z3(p) == p
SPASS(p) == p
LS4(p) == p

\* ----------------------------------------------------------------------
\* Temporal‑logic proof‑rule placeholders.  These operators stand for the
\* standard rules (invariance, well‑formedness, fairness, etc.) that the
\* proof system may invoke.
\* ----------------------------------------------------------------------
Invariance(rule) == rule
WellFormedness(rule) == rule
StrongFairness(rule) == rule
WeakFairness(rule) == rule
StepSimulation(rule) == rule

\* ----------------------------------------------------------------------
\* Fundamental theorems required by the specification.
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAllValues ==
  \A S \in SUBSET UNIV :
    ~(\A x \in UNIV : x \in S)

====