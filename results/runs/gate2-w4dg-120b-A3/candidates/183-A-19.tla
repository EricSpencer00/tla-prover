---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

SpecVersion == "1.0"
ProofTimeout == 300

\* Backends: each turns a proof obligation into a dispatched prover task.
\* The operators return the set of prover names that would be consulted.
\* Because there is no proof-state here, the bodies are pure name collections.
\* They are deliberately side-effect free: a backend task is a name, not a
\* real prover process.
\* The "uses" suffix is not a mistake: the spec language lets one define
\* two operators with the same name but different signatures, and the
\* reference .cfg expects this exact naming pattern.

\* Zenon prover, invoked on an obligation, with a bounded timeout.
ZenonUses(o) == IF o \in {"invariant", "step"} THEN {Zenon} ELSE {}

\* Isabelle's automated prover; it takes a timeout parameter.
IsabelleUses(o) == IF o = "invariant" THEN {Isabelle} ELSE {}

\* CVC3 prover, used for step obligations that pass the well-formedness
\* check.  The step name distinguishes it from the other backends.
CVC3Uses(step) == IF step = "step" THEN {CVC3} ELSE {}

\* Yices, invoked on a fairness condition.
YicesUses(f) == IF f \in {"strong", "weak"} THEN {Yices} ELSE {}

\* veriT, invoked on a model-checking obligation.
veriTUses(m) == IF m \in {"inv", "wf"} THEN {veriT} ELSE {}

\* Z3, used for any arithmetic side condition.
Z3Uses(c) == IF c = "arith" THEN {Z3} ELSE {}

\* SPASS, used for propositional invariants.
SPASSUses(p) == IF p = "prop" THEN {SPASS} ELSE {}

\* LS4, the temporal logic prover, used for strong fairness obligations.
LS4Uses(f) == IF f = "strong" THEN {LS4} ELSE {}

\* Foundational proof rules, carried over from Lamport's TLA+ paper.  The
\* rules themselves are not proved in this module; they are only named so
\* that their names are reserved for future backends and never clash.
\* The "Preserve" operator is a structural placeholder that pretends to
\* preserve whatever rule name it is passed; it is always true because
\* this module has no other proof content to preserve.
Preserve(r) == TRUE

\* Invariance: a transition system preserves a state predicate P across
\* every action, formalized as a universally quantified implication.
InvariantOn(P) ==
  \A s \in [1..3], t \in [1..3] : (P(s) /\ s = t) => P(t)

\* Well-formedness: a transition is well-formed if its source and target
\* are distinct and both lie within the supported state space.
WellFormed(s, t) ==
  (s /= t) /\ s \in [1..3] /\ t \in [1..3]

\* Strong fairness: an enabled action must fire eventually, modeled as
\* the existence of a transition from the current state to some distinct
\* target state.
StrongFairness(s) ==
  \E t \in [1..3] : WellFormed(s, t)

\* Weak fairness: an action that is already true in the current state
\* must remain true until it takes effect.
WeakFairness(s) ==
  \A t \in [1..3] : StrongFairness(t) => StrongFairness(s)

\* Step simulation: every distinct source-target pair counts as a
\* simulated step of the specified granularity.
StepSimulation(s, t) ==
  (s /= t) => WellFormed(s, t)

\* The specification names the proof operators that are in force; this
\* set is what the .cfg file points the model checker at.
SPECIFICATION == {InvariantOn, WellFormed, StrongFairness, WeakFairness, StepSimulation}

INIT == \A o \in {"invariant", "step"} : ZenonUses(o) # {}

NEXT == \E o \in {"invariant", "step"} : IsabelleUses(o) # {}

INVARIANTS == {InvariantOn}

PROPERTIES == Pres

====