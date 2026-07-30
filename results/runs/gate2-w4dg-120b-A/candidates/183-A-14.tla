---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  \* Backend provers and SMT solvers for TLAPS. Declared as constants so that a
  \* later configuration can assign them to concrete solver instances.
  ZENON, ISABELLE, CVC3, YICES, VERIT, Z3, SPASS, LS4

\* Axioms for the primitive temporal operators: always (square) and eventually
\* (diamond). These allow a module to use the operators without importing
\* the full temporal logic library.
Variables
  TRUE
TypeOK == TRUE = TRUE

Box(f, S) == \A x \in S : f[x]
Diamond(f, S) == \E x \in S : f[x]

\* Invariance rule: to prove a property P holds in every reachable state (Box),
\* it suffices to prove P holds initially and that every action preserves P.
Invariance(P) == P /\ (Box(P, { TRUE }) => P)

\* Well-formedness rule: a bounded variable stays within its allowed domain.
WellFormed(var, dom) == Box(Lambda S \in { TRUE } : var \in dom, { TRUE })

\* Strong fairness: whenever a condition becomes true, the action named must
\* eventually happen, even if it is not continuously enabled.
StrongFairness(condition, action) == (condition => Diamond(action, { TRUE }))

\* Weak fairness: an action that is continuously enabled must eventually happen.
WeakFairness(condition, action) == (Box(condition, { TRUE }) => Diamond(action, { TRUE }))

\* Step simulation: a step satisfying the action relation is always possible.
Step(action) == Box(action, { TRUE })

\* The module names no actions or variables of its own; every rule above is
\* a placeholder to reserve the name for a future version.
None == TRUE

Init == None

Next == None

Spec == Init

INVARIANT Extensionality ==
  \A X \in SUBSET S, Y \in SUBSET S : (\A x \in S : (x \in X <=> x \in Y)) => X = Y

INVARIANT NoUniversalSet ==
  \A X \in SUBSET S : (\A x \in S : x \in X) => X = {}

====