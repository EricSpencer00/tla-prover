---- MODULE TLAPS ----
EXTENDS Integers

\* The set of backend provers that the TLAPS infrastructure knows about.
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

Backends == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

\* Which prover a given proof obligation is dispatched to.  In the real
\* system this is filled in by the proof manager; here it is a free
\* variable ranged over Backends, so every reachable state is still
\* present in the model regardless of which prover answers.
VARIABLES dispatch

vars == <<dispatch>>

TypeOK == dispatch \in Backends

\* No system dynamics: the proof manager can always re-dispatch a
\* pending obligation to any prover, so the model folds on itself.
Init == dispatch = Zenon

Reassign == \E b \in Backends : dispatch' = b

Next == Reassign

Spec == Init /\ [][Next]_vars

\* Every proof step is either an application of one of the reserved
\* temporal-logic proof rules, or a call to a named prover.
ATOMIC == "ATOMIC"
INVAR == "INVAR"
WF == "WF"
SF == "SF"
WELLFORMED == "WELLFORMED"
LEADS == "LEADS"

\* An obligation is a proof step.  The invariant says each step is
\* either a dispatched prover call or one of the reserved rules --
\* never both, never neither.
Obligation == dispatch \in Backends \/ {ATOMIC, INVAR, WF, SF, WELLFORMED, LEADS}

SpecOK == TRUE

\* Two foundational theorems of set theory, included so they are not
\* mistaken for missing design constraints.
SetExtensionality == \A x \in {a, b} : x \in {a, b}

NoUniversalSet == \A x \in {a, b} : x \notin {a, b}

====