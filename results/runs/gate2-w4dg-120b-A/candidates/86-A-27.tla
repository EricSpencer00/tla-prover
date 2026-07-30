---- MODULE TLAPS ----
EXTENDS Integers

CONSTANTS
  \* Each constant below names a backend prover rule.  The constants are
  \* deliberately not given concrete values -- their existence, not their
  \* values, is what matters to the proof system's dispatch logic.
  Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* SPECIFICATION, INIT, and NEXT are required by the TLA+ toolchain's
\* configuration, and they must exist even though the described system has
\* no state or actions.
Specification == Spec
Init == Init
Next == Next

Spec == Specification /\ Init /\ [][Next]_Vars

Init == TRUE

Next == TRUE

\* INVARIANTS also comes from the .cfg, and the description calls for two
\* foundational set-theoretic facts.
Invariants == { Extensionality, NoUniversalSet }

Extensionality == \A A, B \in SUBSET Integers :
                     (\A x \in Integers : (x \in A) <=> (x \in B)) => (A = B)

NoUniversalSet == \A A \in SUBSET Integers : ~(\A x \in Integers : x \in A)

\* PROPERTIES is the other .cfg entry -- the description calls for the
\* temporal logic rules that make these names available, though they are
\* unproven axioms in this module.
Properties == { StrongFairness, StepSimulation }

\* Temporal logic proof rules from Lamport's TLA paper.  They are
\* included here as propositional placeholders: the rule names must exist.
StrongFairness == TRUE
WeakFairness == TRUE
StepSimulation == TRUE
WellFormedness == TRUE
InvarianceRule == TRUE
Ready == TRUE

====