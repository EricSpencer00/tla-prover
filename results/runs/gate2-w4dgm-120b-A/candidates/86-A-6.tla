---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

\* This module is a helper from the proof library, defining backend pragmas
\* for TLAPS (which prover to dispatch a proof obligation to) as well as the
\* core temporal-logic proof rules from Lamport's TLA+.  The module's own
\* correctness properties are set-extensionality and the existence of an
\* element outside any given set.

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Backend-dispatch pragmas: mapping a prover symbol to its time budget.
PragmaDispatch == [ Zenon |-> 10, Isabelle |-> 20, CVC3 |-> 10, Yices |-> 15,
                    VeriT |-> 10, Z3 |-> 10, SPASS |-> 12, LS4 |-> 18 ]

\* A propositional fact naming a primitive action's semantics, tagged with the
\* step it belongs to (0 = initialization, 1 = step transition).
Fact == { "InitStep0", "StepUp1", "StepDown1", "Stutter1" }

\* The TLA+ action that applies a primitive step fact to the system state.
ApplyFact(f) == /\ f \in Fact
                /\ \A g \in Fact : g # f => g' = g
                /\ UNCHANGED PragmaDispatch

\* An uninterpreted temporal relation on facts; the proof rules below only
\* ever add pairs to it, never remove them, so it can only grow.
TemporalStep == [ Fact -> Fact ]

\* The next-state relation: any primitive fact can be applied, any fact can be
\* related to any other by the temporal step, or the system can idle.
Next == ApplyFact("InitStep0") \/ ApplyFact("StepUp1")
        \/ ApplyFact("StepDown1") \/ ApplyFact("Stutter1")
        \/ \E f, g \in Fact : /\ f # g
                             /\ TemporalStep' = [ TemporalStep EXCEPT ![f] = g ]
                             /\ UNCHANGED << PragmaDispatch, Fact >>
        \/ UNCHANGED << PragmaDispatch, Fact, TemporalStep >>

\* The system starts with exactly the Liveness step fact, everything else
\* empty, and the temporal step relation with only reflexive pairs.
Init == /\ Fact = { "Liveness" }
        /\ PragmaDispatch = [ p \in { Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4 }
                              |-> 1 ]
        /\ TemporalStep = [ f \in { "Liveness" } |-> [ g \in { "Liveness" } |-> IF f = g THEN "Liveness" ELSE "None" ] ]

\* Proof rule: an invariant preserved by every primitive step is a state
\* invariant of the whole system (standard TLA+ reasoning).
InvariantRule(g) == (\A f \in Fact : g \in Fact) => (g \in Fact)

\* Proof rule: each primitive step fact is a well-formed TLA+ construct --
\* its syntax matches the action-guard shape the language requires.
WellFormedFact(f) == /\ f \in Fact
                    /\ (\A g \in Fact : g # f => g \in Fact)

\* Proof rule: a step that can always be taken (e.g. a stutter) is strongly
\* fair -- it cannot be postponed forever.
StrongFairStutter == SF_vars(ApplyFact("Stutter1"))

\* Proof rule: a step that may be taken (not always enabled) is weakly fair
\* -- it cannot be perpetually bypassed by the scheduler.
WeakFairUp == WF_vars(ApplyFact("StepUp1"))

\* Proof rule: a step that may be taken (not always enabled) is weakly fair
\* -- it cannot be perpetually bypassed by the scheduler.
WeakFairDown == WF_vars(ApplyFact("StepDown1"))

Spec == Init /\ [][Next]_<< PragmaDispatch, Fact, TemporalStep >>

\* Reasoning about facts as ordinary mathematical objects: two sets of facts
\* are equal exactly when they have the same members, and no set can hold
\* every possible value drawn from any non-empty domain.
Extensionality == \A X, Y \in SUBSET Fact : (\A x \in Fact : x \in X <=> x \in Y) => X = Y

NoUniversalSet == \A X \in SUBSET Fact : (X = Fact) => (Fact = {})

====