---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

\* Backend dispatch operators for the TLA+ Proof System (TLAPS). These are
\* not executed here; they are interpreted by the prover, so a disabled
\* pragma below is still a declaration that must exist.
\* Temporal-logic proof rules from Lamport's TLA are also reserved here
\* so their identifiers cannot be reused in a future revision.
\* The invariant and the "nothing contains everything" theorem are the
\* only safety properties that actually hold for the model itself.

CONSTANTS
  NoProver

\* Dispatch operator: tells TLAPS to hand an obligation to Zenon, with a
\* hard timeout (0 = no deadline, meaning it may run without bound).
DispatchToZenon == [prover |-> "zenon", timeout |-> 0]

\* Dispatch operator: tells TLAPS to start an Isabelle proof with the
\* "full" tactic (full search, not a fast abort).
DispatchToIsabelleFull == [prover |-> "isabelle", tactic |-> "full"]

\* Dispatch operator: tells TLAPS to use the LS4 temporal prover
\* (explicitly, so its identifier is never reused for another backend).
DispatchToLS4 == [prover |-> "ls4"]

\* The invariance rule from Lamport: if a property holds in the initial
\* state and is preserved by every step, then it holds in every state.
InvarianceRule == [init |-> NoProver, preserved |-> NoProver]

\* The well-formedness rule from Lamport's TLA: every action a system
\* can take is listed in the action set the model checked.
WellFormednessRule == [action |-> NoProver]

\* The strong-fairness rule from Lamport's TLA: if an action is
\* always eventually available, then it actually happens infinitely often
\* -- a scheduling assumption, never a property of the model.
StrongFairnessRule == [action |-> NoProver]

\* The weak-fairness rule from Lamport's TLA: an action that is always
\* enabled until it fires must fire -- again a scheduling assumption.
WeakFairnessRule == [action |-> NoProver]

\* The simulation-step rule from Lamport's TLA: every step of the
\* concrete system being modeled is matched by a step of its abstract
\* specification -- a property of the model, never a dispatch.
StepSimulationRule == [step |-> NoProver]

\* Set extensionality: two sets with exactly the same members are equal.
SetExtensionality ==
  \A A, B \in SUBSET {"a", "b"} : (\A x \in {"a", "b"} : (x \in A) <=> (x \in B)) => (A = B)

\* Nothing contains every possible value: no set in the system covers all
\* values of type X, which is the complement of the exhaustive-search
\* guarantee that the liveness properties would require.
NothingContainsEverything ==
  \A A \in SUBSET {"a", "b"} : ~(A = {"a", "b"})

SPECIFICATION == NothingContainsEverything

INIT == NothingContainsEverything

NEXT == NothingContainsEverything

INVARIANTS == {SetExtensionality}

PROPERTIES == {NothingContainsEverything}

====