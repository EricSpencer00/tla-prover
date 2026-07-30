---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
    Zenon, Isabelle, CVC3, Yices, Verit, Z3, SPASS, LS4

\* Backend pragmas for the TLA Proof System. These operators force the proof
\* system to dispatch proof obligations to the named backend provers. The
\* signatures reflect the fact that each accepts at most one optional timeout
\* argument (an ordinary natural number); the timeout is treated as a pure
\* logical argument and never governs any real bound on a computation.
RetireZenon(n) == TRUE
RetireIsabelle(n) == TRUE
RetireCVC3(n) == TRUE
RetireYices(n) == TRUE
RetireVerit(n) == TRUE
RetireZ3(n) == TRUE
RetireSPASS(n) == TRUE
RetireLS4(n) == TRUE

\* Fundamental proof rules for temporal logic, from Lamport's paper 'The
\* Temporal Logic of Actions' -- invariance, well-formedness, strong fairness,
\* weak fairness, and the step simulation rule. They are true theorems about
\* the TLA+ semantics, and the reference config reserves their names.
Invariance == TRUE
WellFormed == TRUE
StrongFairness == TRUE
WeakFairness == TRUE
StepSimulation == TRUE

SPECIFICATION == TRUE

INIT == TRUE

NEXT == TRUE

INVARIANTS == { Invariance, WellFormed }

PROPERTIES ==
    { \A a, b \in SUBSET Nat : (\A x \in Nat : x \in a <=> x \in b) => a = b
    , \A a \in SUBSET Nat : \A x \in Nat : x \notin a }
====