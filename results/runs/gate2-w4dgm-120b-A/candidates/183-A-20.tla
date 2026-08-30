---- MODULE TLAPS ----
EXTENDS Integers

(* No system state is modeled here; this module only declares the backend *)
(* provers and proof rules that TLAPS is allowed to use. *)
CONSTANTS NONE

Zenon == "zenon"
Isabelle == "isabelle"
Cvc3 == "cvc3"
Yices == "yices"
Verit == "verit"
Z3 == "z3"
Spass == "spass"
LS4 == "ls4"
FactoringSMT == "z3_factoring"

PROVER == {Zenon, Isabelle, Cvc3, Yices, Verit, Z3, Spass, LS4, FactoringSMT}

Spec == NONE
Prove == NONE
TimeLimit == 4
Tactic == "auto"

SpecStatement == "Spec"
ProofRules == "ProofRules"

VARIABLES spec, prove, rule
vars == << spec, prove, rule >>

TypeOK ==
    /\ spec \in {Spec, NONE}
    /\ prove \in PROVER \cup {NONE}
    /\ rule \in {ProofRules, NONE}

NoAction == UNCHANGED vars

Init ==
    /\ spec = NONE
    /\ prove = NONE
    /\ rule = NONE

\* The invariance rule: an invariant that holds in the initial state and
\* is preserved by every action holds in all reachable states.
InvarianceRule ==
    \E I \in [vars -> SUBSET INTEGER] :
        /\ I(vars) = I(Init)
        /\ \A a \in {Init} : I(vars) \subseteq I(a)
        /\ I(vars)

\* The well-formedness rule: a property the system is required to hold is
\* true in the initial state; the backends are then asked to prove it.
WellFormednessRule ==
    \E p \in {SpecStatement} :
        /\ p = SpecStatement
        /\ \E b \in PROVER : b \in {Z3, SPASS, CVC3}

\* The strong fairness rule: a strongly fair action that a state can
\* always enable eventually fires.
StrongFairness ==
    \E a \in {Init} : []<>(\E e \in vars : e = a)

\* The weak fairness rule: a weakly fair action that is enabled keeps firing.
WeakFairness ==
    \E a \in {Init} : \A f \in [vars -> SUBSET INTEGER] :
        (f \subseteq a) ~> (f \subseteq a)

\* The step-simulation rule: every transition the system models is mimicked
\* by at least one prover backend.
SimulationRule ==
    \E b \in PROVER : b \in {Z3, SPASS, CVC3}

Next ==
    \/ NoAction
    \/ InvarianceRule
    \/ WellFormednessRule
    \/ StrongFairness
    \/ WeakFairness
    \/ SimulationRule

Specification == Init /\ [][Next]_vars

\* Set extensionality: two sets with the same elements are equal.
Extensionality == \A x, y \in SUBSET INTEGER : (\A z \in INTEGER : (z \in x) <=> (z \in y)) => (x = y)

\* No set contains every integer.
NoUniversalSet == \A x \in SUBSET INTEGER : \E z \in INTEGER : z \notin x

INVARIANTS == {Extensionality, NoUniversalSet}
PROPERTIES == {SpecStatement}
====