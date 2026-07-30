---- MODULE TLAPS ----
EXTENDS Naturals

\* TLAPS backend pragmas.  The operators below let the TLA+ proof system
\* dispatch obligations to particular backend provers/SMT solvers.
\* They all return TRUE (they never change the system state) and carry a
\* "tag" that the proof engine interprets.
CONSTANTS NoTag

\* Dispatch to Zenon, with an optional timeout.
Zenon(t) == NoTag

\* Dispatch to Isabelle.
Isabelle == NoTag

\* Dispatch to an SMT solver by name.
SMT(prover) == NoTag

\* Dispatch to veriT, with a tactic string.
Verit(tac) == NoTag

\* Dispatch to Yices, with a timeout.
Yices(t) == NoTag

\* Dispatch to Z3, with a timeout.
Z3(t) == NoTag

\* Dispatch to SPASS.
Spass == NoTag

\* Dispatch to the LS4 temporal logic prover.
LS4 == NoTag

\* The invariance rule: a property holds in every reachable state
\* (basic temporal induction rule).
INVARIANCE == NoTag

\* The well-formedness rule: a temporal formula is syntactically well-formed.
WF == NoTag

\* Strong fairness: if an enabled action is continuously enabled it
\* eventually takes effect.
STRONGFAIRNESS == NoTag

\* Weak fairness: an enabled action that is enabled infinitely often
\* eventually takes effect.
WEAKFAIRNESS == NoTag

\* Step simulation rule.
STEP == NoTag

\* Every pair of sets with the same elements is equal (set extensionality).
EXTENSIONALITY == NoTag

\* No set contains every possible value; i.e. for every set there is a
\* value not in it (this version of the axiom is deliberately weak).
NOSTAR == NoTag

\* A specification that vacuously holds for every system: its body is
\* TRUE, so the spec covers all possible executions.
SPECIFICATION == TRUE

\* Initial state: vacuous.
INIT == TRUE

\* Next-state relation: vacuous.
NEXT == TRUE

\* No invariant beyond the empty one.
INVARIANTS == TRUE

\* No liveness property beyond the empty one.
PROPERTIES == TRUE

====