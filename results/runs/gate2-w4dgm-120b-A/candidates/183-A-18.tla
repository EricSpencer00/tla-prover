---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS Obligation, Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Backend dispatch instructions: how TLAPS routes each obligation to a solver
\* or prover. The definitions are intentionally partial (they are configuration
\* directives rather than functional specifications) so that they can be
\* extended with new solvers or tactics without changing the shape of the
\* module, which is what lets them stay backwards compatible.
Dispatch(z) == IF z = Zenon THEN "use_zenon"
                ELSE IF z = Isabelle THEN "prove_in_isabelle"
                ELSE IF z = CVC3 THEN "solve_in_cvc3"
                ELSE IF z = Yices THEN "solve_in_yices"
                ELSE IF z = VeriT THEN "prove_in_verit"
                ELSE IF z = Z3 THEN "solve_in_z3"
                ELSE IF z = SPASS THEN "prove_in_spass"
                ELSE IF z = LS4 THEN "prove_temporal_in_ls4"
                ELSE "noop"

\* A timed dispatch adds a time budget for solvers that support it.
TimedDispatch(z, t) == IF z \in {Yices, Z3} THEN Dispatch(z) @@ " with timeout " @@ t
                       ELSE Dispatch(z)

\* The temporal logic proof rules (from Lamport's TLA+ paper) are included
\* as reserved names here; they are not given semantics in this module
\* because they live in the underlying logic engine, not the configuration.
INVARIANT == TRUE
WELLFORMED == TRUE
STRONGFAIR == TRUE
WEAKFAIR == TRUE
STEPSIM == TRUE

\* Foundational set-theoretic theorems carried in the standard library.
EXTENSIONALITY == \A X, Y \in SUBSET Obligation : (\A x \in Obligation : x \in X <=> x \in Y) => X = Y
VALUENARROW == ~ \E X \in SUBSET Obligation : \A y \in Obligation : y \in X

\* Spec: what must always hold, and the action set (empty here, since this is
\* a config/logic module with no system dynamics of its own).
Spec == INVARIANT /\ WELLFORMED /\ STRONGFAIR /\ WEAKFAIR /\ STEPSIM /\ EXTENSIONALITY /\ VALUENARROW
NoAction == UNCHANGED <<Dispatch, TimedDispatch>>

\* The config file wires these names up to the proof engine's checking
\* discipline; the module itself does no checking.
SPECIFICATION == Spec
INIT == Spec
NEXT == NoAction
INVARIANTS == EXTENSIONALITY
PROPERTIES == VALUENARROW
====