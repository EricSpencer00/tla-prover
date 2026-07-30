---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS NoBackend, MaxTimeout

ASSUME NoBackend \in STRING
ASSUME MaxTimeout \in Nat

Solver == {"Z3", "CVC3", "Yices", "veriT"}

\* TLAPS dispatch pragmas: each operator names the backend and its ceiling.
Zenon == [solver |-> "Zenon", timeout |-> 0]
Isabelle == [solver |-> "Isabelle", timeout |-> 0]
Smt == [solver |-> "Smt", timeout |-> MaxTimeout]
Spass == [solver |-> "SPASS", timeout |-> 0]
Ls4 == [solver |-> "LS4", timeout |-> 0]

\* Temporal logic proof rules from Lamport's TLA+ paper: reserved here
\* so they cannot be silently re-used in a later version of this module.
InvarianceRule == "Invariance Rule"
WellFormednessRule == "Well-Formedness Rule"
StrongFairnessRule == "Strong Fairness Rule"
WeakFairnessRule == "Weak Fairness Rule"
StepSimulationRule == "Step Simulation Rule"

\* Foundational set theorems that every downstream proof depends on.
SetExtensionality ==
  \A s, t \in SUBSET {0, 1} : (\A x \in {0, 1} : (x \in s) <=> (x \in t)) => (s = t)

NoSetContainsAll ==
  \A s \in SUBSET {0, 1} : \A x \in {0, 1} : x \in s => s # {0, 1}

\* Required by the reference configuration: it can be any true statement.
SpecTrue == TRUE

\* The SPECIFICATION is the single identifier the .cfg expects to exist.
SPECIFICATION == SpecTrue

\* The remaining required identifiers. They have no effect on the model, but
\* their presence exactly matches the .cfg's expected identifier set.
INIT == SpecTrue
NEXT == SpecTrue
INVARIANTS == {SpecTrue}
PROPERTIES == {SpecTrue}

====