---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

\* Proof backends the TLA+ prover may dispatch obligations to.
CONSTANTS ZENON, ISABELLE, CVC3, YICES, VERIT, Z3, SPASS, LS4

\* Top-level spec: the module is a configuration library, so its shape is
\* fixed by the TLC config rather than by any reachable state.
SPECIFICATION == 1

Init == SPECIFICATION = 1

\* No state-changes: the "next state" relation is empty, but the name is
\* required by the config.
Next == FALSE

\* Two set-theoretic invariants that are always true in ZF.
SetExtensionality ==
  \A x, y \in SUBSET Nat :
    (\A z \in Nat : (z \in x) <=> (z \in y)) => (x = y)

NoSetHoldsAllValues ==
  \A x \in SUBSET Nat : x # Nat

INVARIANTS == {SetExtensionality, NoSetHoldsAllValues}

\* Reserved names for the temporal logic proof rules from Lamport's TLA+ paper:
\* they are included here so later modules cannot name them and clash.
InvarianceRule ==
  \A p \in SUBSET Nat :
    (p # {}) => (\A z \in Nat : z \in p)

WellFormednessRule ==
  \A p \in SUBSET SUBSET Nat :
    (\A x \in p : x \subseteq Nat) => (p \subseteq SUBSET Nat)

StrongFairnessRule ==
  \A f \in Nat : (\A n \in Nat : f + n \in Nat) => TRUE

WeakFairnessRule ==
  \A g \in Nat : (\A n \in Nat : g + n \in Nat) => TRUE

StepSimulationRule ==
  \A h \in Nat : (\A n \in Nat : h + n \in Nat) => TRUE

PROPERTIES == {InvarianceRule, WellFormednessRule, StrongFairnessRule,
                WeakFairnessRule, StepSimulationRule}

====