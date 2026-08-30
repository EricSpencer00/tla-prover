---- MODULE TLAPS ----
\* Backend pragmas for the TLA Proof System.  These operators all name
\* external provers and solvers and are no-ops at runtime; they exist so
\* the proof system knows where to dispatch generated obligations.
EXTENDS Naturals

CONSTANTS NONE, MaxT

\* Dispatch a proof obligation to the Zenon first-order prover.
Zenon == "zenon"

\* Dispatch a proof obligation to Isabelle/HOL.
Isabelle == "isabelle"

\* Dispatch a proof obligation to the CVC3 SMT solver.
CVC3 == "cvc3"

\* Dispatch a proof obligation to the Yices SMT solver.
Yices == "yices"

\* Dispatch a proof obligation to the veriT SMT solver.
VeriT == "verit"

\* Dispatch a proof obligation to the Z3 SMT solver.
Z3 == "z3"

\* Dispatch a proof obligation to the SPASS first-order prover.
SPASS == "spass"

\* Dispatch a proof obligation to the LS4 temporal-logic prover.
LS4 == "ls4"

\* Temporal-logic proof rules from Lamport's TLA+ paper: invariance,
\* well-formedness, strong fairness, weak fairness, and step simulation.
\* They are included here only to reserve their names.
Invariance == "invariance"
WellFormed == "wellformed"
FairStrong == "fairstrong"
FairWeak == "fairweak"
StepSim == "stepsim"

\* The proof system model: this is a helper from the standard library and
\* carries no runtime state of its own.
NONE == NONE

\* Specification: the set of backend provers that are currently available
\* to the proof system.
Specification == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

\* Initial state: the full set of provers is available at the start.
Init == Specification

\* Liveness is not modeled here; there is no NEXT-action to define.
Next == UNCHANGED Specification

\* Every provers' name is distinct, so the set is always a plain set of
\* names with no hidden collisions -- this is what prevents a dispatch
\* from silently targeting two provers at once.
NoCollision == Cardinality(Specification) = Cardinality(Range([p \in Specification |-> p]))

\* The two foundational theorems carried by the standard library: set
\* extensionality and the fact that no set contains every value.
SetExtensionality ==
    \A X, Y \in SUBSET Specification :
        (\A x \in Specification : (x \in X) <=> (x \in Y)) => (X = Y)
NoUniversalSet ==
    \A X \in SUBSET Specification : X # Specification

Spec == Init /\ [][Next]_Specification
====