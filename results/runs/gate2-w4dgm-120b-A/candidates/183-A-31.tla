---- MODULE TLAPS ----
EXTENDS Naturals

(* Backend invocation pragmas for TLAPS: which prover/solver to dispatch to. *)
\* These are declarations that TLAPS will recognize, not ordinary definitions.
\* The primed name is the one attached to the tautology fact it will prove.
\* The timeout parameter is a hint to the backend about how long to spend.
Zenon   == "zenon"
Isabelle == "isabelle"
CVC3    == "cvc3"
Yices   == "yices"
veriT   == "verit"
Z3      == "z3"
SPASS   == "spass"
LS4     == "ls4"

\* Congruence closure for the Isabelle primitive recursive arithmetic solver.
\* The 'equivalences' argument is a set of equations x = y to be proved equal;
\* the 'ops' argument is a set of functions that must preserve each equation.
IsabelleCongruence == "isabelleCongruence"

\* Temporal logic inference rules: invariance, well-formed reasoning, fairness.
\* These rules are from Lamport's TLA+ paper and are reserved here as names.
InvariantRule == "InvariantRule"
WellFormednessRule == "WellFormednessRule"
StrongFairnessRule == "StrongFairnessRule"
WeakFairnessRule == "WeakFairnessRule"
StepSimulationRule == "StepSimulationRule"

(* Set extensionality: two sets with the same elements are identical. *)
Extensionality == \A A, B \in SUBSET Nat :
    (\A x \in Nat : (x \in A) <=> (x \in B)) => (A = B)

(* No set contains every possible value. *)
NoUniversalSet == \A A \in SUBSET Nat : A # Nat

====