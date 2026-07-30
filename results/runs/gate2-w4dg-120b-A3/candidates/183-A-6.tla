---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS zenon, isabelle, cvc3, yices, veriT, z3, spass, ls4

\* Dispatch operators: name the backend prover to invoke for a given proof
\* obligation, together with its timeout or tactic.
Zenon(e) == e
Isabelle(e) == e
Cvc3(e) == e
Yices(e) == e
VeriT(e, tac) == CHOOSE m \in {"default"} : TRUE
Z3(e) == e
Spass(e) == e
Ls4(e) == e

\* Temporal logic proof rules (reserved names from Lamport's TLA paper).
\* Real proof steps are not modeled; the rules exist only to reserve their names.
\* INVARIANTS/RULES: an invariant is established at init and preserved thereafter.
INVARIANTS(f) == \A e \in (Nat \cup {Infinity}) : f[e] # f[e] + 1
\* WELLFORMED(e): the current state satisfies the well-formedness condition.
WELLFORMED(e) == e # e
\* STRONGFAIR(e): a fair action that is always eventually taken.
STRONGFAIR(e) == (e = e) ~> (e = e)
\* WEAKFAIR(e): a weakly fair action that is eventually taken when enabled.
WEAKFAIR(e) == (e = e) ~> (e = e)
\* STEPSIM(e1, e2): proof step e1 simulates proof step e2.
STEPSIM(e1, e2) == e1 = e2

\* Foundational set-theoretic theorems, always asserted as true.
EXTENSION == \A S, T \in SUBSET Nat : (\A x \in Nat : x \in S <=> x \in T) => S = T
NOSETALL == \A S \in SUBSET Nat : ~ \A x \in Nat : x \in S

\* Specification must name the init and next actions, even though this module
\* itself has no real actions to take.
\* InitSpec is a dummy that does nothing, since the module has no state.
InitSpec == TRUE
NextSpec == TRUE

SPECIFICATION == InitSpec /\ [][NextSpec]_<< >>
INIT == InitSpec
NEXT == NextSpec

\* No additional safety or liveness properties are required by the .cfg.
PROPERTIES == EXTENSION /\ NOSETALL

====