---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Backend prover dispatch operators (placeholders)
\* ----------------------------------------------------------------------
Zenon(p)      == TRUE            \* Dispatch proof obligation p to Zenon
Isabelle(p)   == TRUE            \* Dispatch proof obligation p to Isabelle
CVC3(p)       == TRUE            \* Dispatch proof obligation p to CVC3
Yices(p)      == TRUE            \* Dispatch proof obligation p to Yices
veriT(p)      == TRUE            \* Dispatch proof obligation p to veriT
Z3(p)         == TRUE            \* Dispatch proof obligation p to Z3
SPASS(p)      == TRUE            \* Dispatch proof obligation p to SPASS
LS4(p)        == TRUE            \* Dispatch proof obligation p to LS4 (temporal)

\* ----------------------------------------------------------------------
\* Fundamental temporal‑logic proof rules (placeholders)
\* ----------------------------------------------------------------------
InvarianceRule(Inv, Init, Next) ==
    /\ Inv \in [<<>> -> BOOLEAN]          \* Invariant predicate
    /\ Init \in [<<>> -> BOOLEAN]         \* Initial condition
    /\ Next \in [<<>> -> BOOLEAN]         \* Next‑state relation
    TRUE

WellFormednessRule(Spec) ==
    Spec \in Spec               \* Placeholder for well‑formedness of a spec
    TRUE

StrongFairnessRule(Fair, Spec) ==
    Fair \in BOOLEAN
    Spec \in Spec
    TRUE

WeakFairnessRule(Fair, Spec) ==
    Fair \in BOOLEAN
    Spec \in Spec
    TRUE

StepSimulationRule(Sim, Impl, Spec) ==
    Sim \in BOOLEAN
    Impl \in Spec
    Spec \in Spec
    TRUE

\* ----------------------------------------------------------------------
\* Foundational theorems
\* ----------------------------------------------------------------------
SetExtensionality ==
    \A S, T \in SUBSET UNIV :
        (\A x : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
    \A S \in SUBSET UNIV : \E x \in UNIV : x \notin S

\* ----------------------------------------------------------------------
\* Exported identifiers (none required by the .cfg, but we expose the
\* theorems and backend operators for completeness)
\* ----------------------------------------------------------------------
THEOREM SetExtensionalityIsValid == SetExtensionality
THEOREM NoUniversalSetIsValid == NoUniversalSet

====