---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Backend pragma operators for TLAPS.  Each simply returns its argument;
\* they act as placeholders for the real proof‑system directives.
\* ----------------------------------------------------------------------
Zenon(p)    == p
Isabelle(p) == p
CVC3(p)     == p
Yices(p)    == p
VeriT(p)    == p
Z3(p)       == p
SPASS(p)    == p
LS4(p)      == p

\* ----------------------------------------------------------------------
\* Fundamental theorems
\* ----------------------------------------------------------------------
SetExtensionality ==
    \A S, T \in SUBSET UNIV :
        (\A x : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
    \A S : \E x \in UNIV : x \notin S

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rules (names reserved for future use)
\* ----------------------------------------------------------------------
InvariantRule(P) ==
    [] (P => [] P)

WellFormednessRule ==
    TRUE

StrongFairnessRule ==
    TRUE

WeakFairnessRule ==
    TRUE

StepSimulationRule ==
    TRUE

\* ----------------------------------------------------------------------
\* Trivial state machine (no variables) required for the standard
\* identifiers SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES.
\* ----------------------------------------------------------------------
Init == TRUE
Next == TRUE

SPECIFICATION == Init /\ [][Next]_{<<>>}

INVARIANTS == {}
PROPERTIES == {}

====