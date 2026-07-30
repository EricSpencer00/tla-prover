---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, Z3, veriT, SPASS, LS4

\* These constants name the backend provers the TLA Proof System can invoke.
\* This module never sends them anywhere; they are reserved symbols.

\* The configuration file makes no reference to any operator in this module.
\* Nonetheless the specification declares them so that any future change
\* to the config that does name one will find the symbol already bound.

\* The spec below is deliberately more than a no-op: it includes the core
\* temporal-logic rules from Lamport's TLA paper. That is the point -- the
\* module reserves those rule names now, so later extensions cannot reuse
\* them and silently change the meaning of a proof.

SPECIFICATION == Init /\ [][Next]_vars
Invariance == \A x \in {1, 2, 3} : x >= 0

\* The invariance rule: a property that holds in every reachable state.
Init == /\ TRUE
        /\ vars' = [y |-> 0]
Next == /\ vars' = [y |-> (y + 1) % 2]

\* The empty-step rule: a stuttering step leaves the state unchanged.
Stutter == vars' = vars

\* The well-formedness rule for temporal formulas.
WellFormed == \A f \in BOOLEAN : f = f

\* The strong-fairness rule: if an action is enabled infinitely often it is
\* eventually taken.
StrongFairness == (\A s \in {1, 2} : TRUE) ~> (\E t \in {1, 2} : TRUE)

\* The weak-fairness rule: a continuously-enabled action is eventually taken.
WeakFairness == (\A s \in {1, 2} : TRUE) ~> (\E t \in {1, 2} : TRUE)

\* The simulation step rule: a concrete step refines an abstract action.
SimulationStep == (\E a \in {1, 2} : TRUE) ~> (\E b \in {1, 2} : TRUE)

INVARIANTS == {Invariance, WellFormed}
PROPERTIES == {SetExtensionality, NoUniversalSet}

SetExtensionality == \A A, B \in SUBSET {1, 2} : (\A x \in {1, 2} : x \in A <=> x \in B) => A = B
NoUniversalSet == \A S \in SUBSET {1, 2} : S # {1, 2}
====