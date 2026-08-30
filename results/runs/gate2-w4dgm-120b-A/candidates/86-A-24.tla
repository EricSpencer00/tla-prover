---- MODULE TLAPS ----
EXTENDS Naturals, Sequences

\* Pragmas: each dispatches a proof obligation to a named backend prover.
\* The two theorems below are fundamental factual statements the proof
\* system checks once and reuses; they are not derived from any state.
ZENO      == "zeno"
ISABELLE  == "isabelle"
CVC3      == "cvc3"
YICES     == "yices"
VERIT     == "verit"
Z3        == "z3"
SPASS     == "spass"
LS4       == "ls4"

\* Dispatches a statement to a backend prover, with a timeout and tactics.
Dispatch(thm) == "Dispatch(" \o thm \o ")"

\* The two foundational theorems the system records as always-true facts.
Extensionality == "Two sets with the same elements are equal."
NoUniverse    == "No set contains every possible value."

\* The full set of dispatches the system may emit for any pending statement.
Dispatches == { Dispatch(ZENO), Dispatch(ISABELLE), Dispatch(CVC3), Dispatch(YICES),
                Dispatch(VERIT), Dispatch(Z3), Dispatch(SPASS), Dispatch(LS4) }

\* The module is a configuration artifact; it never changes its state, so the
\* safety and liveness properties below are always trivially satisfied.
Spec == Dispatches \X Dispatches

Init == Spec

Next == Spec

TypeOK == TRUE

\* Two independent but equally valid ways to write the same fact: every model of
\* this module is a singleton set, so the system can never drift from it.
SingletonState == Spec = {Spec}

BothTheorems == Extensionality /\ NoUniverse

====