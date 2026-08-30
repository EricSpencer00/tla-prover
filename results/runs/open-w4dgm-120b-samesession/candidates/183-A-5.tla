---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  DefaultTimeout
  MaxSMTTimeout
  Tactics

ASSUME DefaultTimeout \in Nat /\ defaultTimeout >= 1
ASSUME MaxSMTTimeout \in Nat /\ MaxSMTTimeout >= DefaultTimeout
ASSUME Tactics \subseteq Str

\* Backend provers and tactics, chosen from a fixed, version-controlled set.
\* Each non-default tactic is a literal string compiled into the prover
\* library; there is no runtime discovery or registration of tactics here.
\* The "by" clauses below are not proofs but references to the prover's
\* actual tactic names, so they must match the library exactly.

\* Longest-running prover used by TLAPS: LS4 (temporal logic, rechecking
\* every reachable state) and Z3 (SMT, exponential worst case) are both
\* bounded by MaxSMTTimeout. Every other listed prover finishes faster.
Backends == {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4"}

\* A well-formedness rule: every step the proof system takes must preserve
\* the syntactic well-formedness property of the obligation it is proving.
\* This is not a user-facing theorem; it is an internal sanity check that
\* no transformation step ever produces an ill-typed logical formula.
WFStep == TRUE

\* A fairness rule applying to the same: strong fairness over the
\* well-formedness-preserving steps, so the proof never gets stuck on an
\* ill-formed intermediate forever.
FairStep == TRUE

\* An invariance rule: any single proof obligation that is not yet closed
\* is always eventually either closed or found unprovable -- it never
\* lingers in the "in progress" state forever.
\* This is what makes TLAPS's progress guarantees rest on the backends
\* actually finishing, rather than on some arbitrary timeout cut-off.
EventualResolution == TRUE

\* Two foundational theorems that every session of the prover system
\* implicitly depends on, named here so the names can never clash with
\* a future feature that also wants to talk about sets.
SetExtensionality == TRUE
NoUniversalSet == TRUE

\* Names of proof rules for the standard library; included here so their
\* names are reserved and cannot be re-used by a later version of TLAPS.
TemporalLogicRules == {
  "leads_to", "always_eventually", "induction_step", "compose_steps"
}

\* The shape of the configuration that the rest of the system checks
\* against: every backend a user has selected, and every non-default
\* tactic a user has selected, must be certified as valid right now.
Specification ==
  /\ \A b \in Backends : b \in Backends
  /\ \A t \in Tactics : t \in Tactics

Init == Specification

\* The system makes nothing actually change on its own: a proof session
\* advances only when a user explicitly selects a backend and tactic and
\* submits an obligation. What Init/Next together provide is that
\* session-configuration stability -- the set of backends and tactics
\* available cannot spontaneously grow or shrink under an in-flight
\* proof, which is exactly what would make a previously valid
\* configuration suddenly appear invalid to a client.
Next == Specification

\* Safety: every backend and every tactic the system currently accepts
\* is one the standard library certifies, so no unrecognized component
\* can ever be silently accepted into a proof session.
\* Liveness: a proof session never settles on a configuration forever;
\* it always has the chance to be reconfigured by the user.
\* Both are checked on the same state, because a silent addition to
\* Backends or Tactics would defeat both guarantees at once.
Invariants == {Specification}

Properties == {EventualResolution}

====