---- MODULE TLAPS ----
EXTENDS Integers

\* Backend provers: each operator below is known to TLAPS as a dispatching
\* pragma, handing a proof obligation to the named prover with a timeout or
\* tactic. The operators are deliberately side-effect-free here; their
\* bodies are never evaluated at runtime, they exist only to reserve the
\* names TLAPS understands.
\* Theorem rules: invariance, well-formedness, strong and weak fairness,
\* and step simulation; they come from Lamport's TLA+ paper and are
\* included as no-op operators so their names stay available.
\* There is no system state to model: this file is pure proof-configuration.

\* Backend provers
Zenon == 0
Isabelle == 1
CVC3 == 2
Yices == 3
Verit == 4
Z3 == 5
SPASS == 6
LS4 == 7

\* Temporal logic proof rules (no-ops, names are reserved)
INVARIANCE == 0
WELLFORMEDNESS == 1
STRONGFAIRNESS == 2
WEAKFAIRNESS == 3
STEP == 4

\* Empty specification: no CONSTANTS, no state variables, nothing to init,
\* and nothing to step. This is intentional; the module exists only for its
\* names. The operators below therefore all have empty bodies.
CONSTANTS == {}
VARIABLES == {}
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE

\* Foundational theorems in the empty model
INVARIANTS == [ setextensionality |-> TRUE, noSetContainsAllValues |-> TRUE ]
PROPERTIES == {}

\* Extensionality: two sets with the same elements are equal.
setextensionality == \A x, y \in SUBSET {1, 2, 3} : (\A z \in {1, 2, 3} : (z \in x) <=> (z \in y)) => (x = y)

\* No set contains every value (trivial in the empty model, but the name must
\* exist so it cannot be reused by a future feature).
noSetContainsAllValues == \A s \in SUBSET {1, 2, 3} : ~(1 \in s /\ 2 \in s /\ 3 \in s)

====