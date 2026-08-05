---- MODULE TLAPS ----
EXTENDS Naturals

\* Backend provers: operators that TLAPS recognizes to dispatch proof obligations.
\* Temporal logic proof rules: the theorems that TLAPS itself takes as primitive
\* for reasoning about TLA+ actions and fairness.

CONSTANTS
  \* Naming the backend provers that this module's operators refer to.
  Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

None == 0

Init ==
  \* The init clause is required syntactically but carries no semantics here, so
  \* it introduces a dummy always-true fact.
  None = None

Next ==
  \* The next clause is required syntactically but carries no semantics here, so
  \* it steps between two states that are both indistinguishable from each other.
  True

Spec ==
  Init /\ [][Next]_None

\* Frontends: operators that a TLA+ proof may invoke to hand an obligation to
\* a concrete backend prover, possibly with a timeout or a tactic hint.
ZenonBackend == TRUE
ZenonWithTimeout == TRUE
IsabelleBackend == TRUE
CVC3Backend == TRUE
YicesBackend == TRUE
VeriTBackend == TRUE
Z3Backend == TRUE
SPASSBackend == TRUE
LS4Backend == TRUE

\* Temporal logic proof rules: the theorems TLAPS assumes as primitive, listed
\* here so their names are reserved and never clash with a future definition.
()\{invariance\} : TRUE
()\{wellFormed\} : TRUE
()\{strongFairness\} : TRUE
()\{weakFairness\} : TRUE

\* A set-extensionality theorem and a non-universality fact are included so
\* the module always carries at least one non-trivial type-correct theorem.
Extensionality ==
  \A X, Y \in SUBSET {1, 2, 3} : (\A e \in {1, 2, 3} : e \in X <=> e \in Y) => X = Y

NonUniverse ==
  \A X \in SUBSET {1, 2, 3} : X = {1, 2, 3} => FALSE

THEOREMS
  Extensionality
  NonUniverse

====