---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT UNIV

(*-----------------------------------------------------------------------
Backend pragma operators for TLAPS.
These are placeholders; the actual implementation is provided by the
proof system. They are defined here so their names are reserved.
-----------------------------------------------------------------------*)
Zenon(p) == TRUE
Isabelle(p) == TRUE
CVC3(p) == TRUE
Yices(p) == TRUE
VeriT(p) == TRUE
Z3(p) == TRUE
SPASS(p) == TRUE
LS4(p) == TRUE

(*-----------------------------------------------------------------------
Temporal‑logic proof‑rule names (reserved only)
-----------------------------------------------------------------------*)
InvariantRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

(*-----------------------------------------------------------------------
Foundational theorems
-----------------------------------------------------------------------*)
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAllValues ==
  \A S \in SUBSET UNIV :
    ~(\A x \in UNIV : x \in S)

(*-----------------------------------------------------------------------
Skeleton identifiers (not required by the .cfg but provided for completeness)
-----------------------------------------------------------------------*)
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====