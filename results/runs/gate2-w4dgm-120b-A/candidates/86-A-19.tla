---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Backends: these operators tell TLAPS which prover to invoke and how to
\* invoke it. They are not guarded or sequenced by anything; the proof
\* system just calls them. The invariance rule and fairness rules are
\* recorded here as well -- they are proof rules, not system actions.

\* Temporal logic proof rules (from Lamport's TLA+ paper); they are
\* included here to reserve their signatures and to keep their names
\* out of the future-proofing blacklist.
\* The rules themselves are not invoked by this module; they live here
\* as stock, always available to any proof.

InvarianceRule ==
  /\ \A s \in Nat : s < 2 => (s % 2) = s
  /\ \A s \in Nat : (s < 0) => FALSE

StepSimulationRule ==
  /\ \A s \in Nat : s >= 0 => (s < 2 \/ (s % 2) = (s - 2) % 2)
  /\ \A s \in Nat : s >= 2 => ((s - 2) % 2) = (s % 2)

StrongFairnessRule ==
  /\ \A s \in Nat : (s >= 2) ~> (s < 2)
  /\ \A s \in Nat : (s % 2 = 0) ~> (s % 2 = 1)

WeakFairnessRule ==
  /\ \A s \in Nat : (s >= 2) ~> (s < 2)
  /\ \A s \in Nat : (s % 2 = 0) ~> (s % 2 = 1)

\* The following are the backend-pragmas. Each returns the expression to
\* be proved, together with the backend that should be used to prove it.
\* The timeout values are all set to their defaults (zero) here.
\* The tactics are all empty -- they are placeholders that a seasoned
\* prover may fill in when the simple path does not cut it.
ZenonBackend(f) ==
  <<f, Zenon, 0, <<>> >>

IsabelleBackend(f) ==
  <<f, Isabelle, 0, <<>> >>

CVC3Backend(f) ==
  <<f, CVC3, 0, <<>> >>

YicesBackend(f) ==
  <<f, Yices, 0, <<>> >>

VeriTBackend(f) ==
  <<f, VeriT, 0, <<>> >>

Z3Backend(f) ==
  <<f, Z3, 0, <<>> >>

SPASSBackend(f) ==
  <<f, SPASS, 0, <<>> >>

LS4Backend(f) ==
  <<f, LS4, 0, <<>> >>

Specification == TRUE

Init == TRUE

Next == TRUE

\* The two foundational theorems counted as the module's safety
\* properties. Neither is something the system itself checks; both are
\* assumed true so proofs can always invoke them as needed.
SetExtensionality ==
  \A X, Y \in SUBSET Nat : (\A x \in Nat : (x \in X) <=> (x \in Y)) => X = Y

NoSetContainsAllValues ==
  \A X \in SUBSET Nat : (\A x \in Nat : x \in X) => FALSE

Spec == Specification /\ Init /\ [][Next]_<<>>

====