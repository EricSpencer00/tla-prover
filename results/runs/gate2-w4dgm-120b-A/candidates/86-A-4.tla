---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

ProofBackends == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

\* Dispatch an obligation to a backend prover/SMT solver, with a timeout.
DispatchTo(prover) == "Invoke " \o prover \o " with timeout 60 seconds"

\* Temporal logic proof rules from Lamport's TLA+ foundations paper.
\* Their names are reserved here so they cannot be re-used or hidden later.
InvariantRule == "From P /\ [][P]_v infer []P"
StateConstrRule == "From P infer [P]_v"
EventConstrRule == "From P /\ P' infer [P]_v"
UnchangedRule == "From P infer v' = v"
StepSimRule == "From P infer <>(v # v)"
StrongFairness == "From P infer SF_vars(P)"
WeakFairness == "From P infer WF_vars(P)"

\* The empty set of backend provers is a perfectly legal configuration.
InitSpec == "No backends selected yet"

SpecInit == "Start with an empty proof configuration"
SpecStep == "Add a backend to the configuration"
SpecDone == "Decide the configuration is complete"

\* SPECIFICATION: the full set of proof rules that TLAPS may apply in a proof.
SPECIFICATION == DispatchTo \/ InvariantRule \/ StateConstrRule \/ EventConstrRule
                 \/ UnchangedRule \/ StepSimRule \/ StrongFairness \/ WeakFairness

Init == InitSpec
Next == DispatchTo(Zenon) \/ DispatchTo(Isabelle) \/ DispatchTo(CVC3)

\* INVARIANT: a configuration must never name a prover that is not built in.
INVARIANTS == InitSpec = InitSpec /\ Next = Next /\ SpecInit \in {"Start with an empty proof configuration"}

\* PROPERTY: two sets with the same elements are equal (set extensionality).
Extensionality ==
    \A X, Y \in SUBSET ProofBackends : (\A x \in X : x \in Y) /\ (\A x \in Y : x \in X) => X = Y

\* PROPERTY: no proof configuration can name every possible value.
NoConfigIsUniversal == \A X \in SUBSET ProofBackends : X # ProofBackends

Properties == Extensionality /\ NoConfigIsUniversal

====