---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  veritTimeout, z3Timeout

\* Both SMT backends use the same timeout, so the two constants share the
\* same value in the model, but they remain separate identifiers.
Values == 0..1

CONSTANTS
  cvc3, yices, verit, z3

\* A backend prover is identified by the constant that names it; the values
\* are constants rather than free variables.
Backends == {cvc3, yices, verit, z3}

MaxTime == 2

VARIABLES used, timeBound

vars == << used, timeBound >>

TypeOK ==
  /\ used \subseteq Backends
  /\ timeBound \in 0..MaxTime

\* No obligations are ever outstanding; the module's only job is to name
\* the backends that TLAPS may invoke.
Init ==
  /\ used = {}
  /\ timeBound = 0

\* Dispatch a proof obligation to a backend that has not yet been used.
Dispatch(b) ==
  /\ b \notin used
  /\ used' = used \cup {b}
  /\ UNCHANGED timeBound

\* Retune the global timeout for the SMT backends.
Retune ==
  /\ timeBound' \in Values
  /\ UNCHANGED used

Next ==
  \/ \E b \in Backends : Dispatch(b)
  \/ Retune

Spec == Init /\ [][Next]_vars

\* The two foundational set-theoretic theorems that the proof library
\* reserves are stated here as plain theorems, not as obligations.
Extensionality ==
  \A A, B \in SUBSET Backends : (A \subseteq B /\ B \subseteq A) => (A = B)

NoUniversalSet ==
  \A S \in SUBSET Backends : S # Backends

====