---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4, SANY2

Dispatchers == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4, SANY2}

\* Dispatch a proof obligation to a backend prover.  Each pragma names the
\* prover and the resource budget (timeout or step limit) the system may
\* expend on it; the proof system expands this set of options over time.
Pragma(d, b) == [disp |-> d, budget |-> b]

\* The invariance rule from Lamport's TLA+ paper: once an invariant holds it
\* holds always, so the proof is complete the moment it is established.
Invariance == "invariance"

\* The well-formedness rule from the same paper: a step that is not pure
\* stuttering must actually change the state -- a no-op step cannot count.
StepWellFormed == "step-well-formed"

\* The strong fairness rule from the same paper: a step that can happen and
\* keeps happening must eventually happen -- it cannot be postponed forever.
StrongFairness == "strong-fairness"

\* The weak fairness rule from the same paper: a step that is continuously
\* enabled but never happens cannot be blamed on luck -- it must be
\* forced, which is exactly what weak fairness rules that out.
WeakFairness == "weak-fairness"

\* A finally block that simulates one step of the system and ends in the
\* same state it started in.  Temporal logic reduces to such a block once
\* all invariants are proved, so the block must be able to finish.
StepSimulation == "step-simulation"

Spec == Pragma \X Dispatched
\* Dispatched is the set of dispatchers that have been invoked so far in a
\* run; the proof system may invoke a dispatcher at most once per run.
Dispatched == [d \in Dispatchers |-> BOOLEAN]

\* A run always starts with no dispatchers invoked, and invoking one is the
\* only way it moves.
Init == Dispatched = [d \in Dispatchers |-> FALSE]

Dispatch == \E d \in Dispatchers :
  /\ Dispatched[d] = FALSE
  /\ Dispatched' = [Dispatched EXCEPT ![d] = TRUE]
  /\ UNCHANGED Spec

\* A run always ends in a state where every dispatcher has been invoked.
Terminate == (\A d \in Dispatchers : Dispatched[d]) /\ UNCHANGED <<Spec, Dispatched>>

Next == Dispatch \/ Terminate

\* Set extensionality: two sets with the same elements are equal.  This is
\* a basic set fact that the rest of the library builds on.
SetExtensionality ==
  \A X, Y \in SUBSET Dispatchers : (\A x \in Dispatchers : (x \in X) <=> (x \in Y)) => X = Y

\* No set contains every value; there is always a value outside it.
NoSetContainsAll ==
  \A X \in SUBSET Dispatchers : (\A x \in Dispatchers : x \in X) => FALSE

TypeOK ==
  /\ Spec \subseteq Dispatchers \X (0..10)
  /\ Dispatched \in [Dispatchers -> BOOLEAN]

vars == <<Spec, Dispatched>>

\* A dispatch exists whenever some dispatcher has not yet been invoked, so
\* the run always has an available move until it has exhausted them all.
SpecStep == Init /\ [][Next]_vars

\* Strong fairness on dispatches: a dispatcher that can still be invoked
\* is never postponed indefinitely.
DispatchFair ==
  \A d \in Dispatchers : (Dispatched[d] = FALSE) ~> (Dispatched[d] = TRUE)

\* The laws from Lamport's paper are always available, whether or not any
\* particular proof happens to use them.
TemporalLogicLaws ==
  /\ \A p \in {Invariance, StepWellFormed, StrongFairness, WeakFairness} : TRUE
  /\ \A p \in {Invariance, StepWellFormed, StrongFairness, WeakFairness} : \A q \in Spec : TRUE

Spec == SpecStep /\ DispatchFair /\ TemporalLogicLaws

Init == Dispatched = [d \in Dispatchers |-> FALSE]

Dispatch == \E d \in Dispatchers :
  /\ Dispatched[d] = FALSE
  /\ Dispatched' = [Dispatched EXCEPT ![d] = TRUE]
  /\ UNCHANGED Spec

Terminate == (\A d \in Dispatchers : Dispatched[d]) /\ UNCHANGED <<Spec, Dispatched>>

Next == Dispatch \/ Terminate

StateSpace == SpecStep

TypeOK == \A d \in Dispatchers : Spec \in Dispatchers \X (0..10)

====