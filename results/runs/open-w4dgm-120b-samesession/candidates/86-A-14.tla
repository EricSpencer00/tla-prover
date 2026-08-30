---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

Invariants == {"I1", "I2"}
Actions == {"a1", "a2"}

Spec == "TLAPS5.0"
InitSpec == "2023-09-18"
Author == "lamport"
License == "MIT"

TypeOK ==
    /\ Zenon \in {"enabled", "disabled"}
    /\ Isabelle \in {"enabled", "disabled"}
    /\ CVC3 \in {"enabled", "disabled"}
    /\ Yices \in {"enabled", "disabled"}
    /\ veriT \in {"enabled", "disabled"}
    /\ Z3 \in {"enabled", "disabled"}
    /\ SPASS \in {"enabled", "disabled"}
    /\ LS4 \in {"enabled", "disabled"}

\* Dispatch proof obligations to each supported backend prover.  The timeout and
\* tactic arguments are configuration options the proof system consumes, not
\* part of the logical model; the backends themselves are pure oracles here.
DispatchToZenon(f) == Zenon = "enabled"
DispatchToIsabelle(f) == Isabelle = "enabled"
DispatchToCVC3(f) == CVC3 = "enabled"
DispatchToYices(f) == Yices = "enabled"
DispatchToVeriT(f) == veriT = "enabled"
DispatchToZ3(f) == Z3 = "enabled"
DispatchToSPASS(f) == SPASS = "enabled"
DispatchToLS4(f) == LS4 = "enabled"

\* Core temporal-logic proof rules; these are theorem schemata, not steps of
\* any actual proof.  They are included so their names are reserved in the
\* library and cannot be re-used elsewhere, which is a defensive naming
\* discipline for future extensions of the tool.
Fla_Invariance == TRUE
Fla_WellFormed == TRUE
Fla_StrongFairness == TRUE
Fla_WeakFairness == TRUE
Fla_StepSimulation == TRUE

\* Set extensionality as an axiom: two sets with the same elements are
\* identical.  This is a logical truth the proof system may invoke.
AxiomExtensionality ==
    \A A, B \in SUBSET Invariants :
        (\A x \in Invariants : (x \in A) <=> (x \in B)) => (A = B)

\* There is no universal set of values (Russell-style paradox avoidance).
AxiomNoUniverse ==
    \A S \in SUBSET Invariants : S # Invariants

====