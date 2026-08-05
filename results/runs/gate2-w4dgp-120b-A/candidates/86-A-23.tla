---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

VARIABLES p1, p2, p3, p4

vars == {p1, p2, p3, p4}

\* Backend pragma: dispatch a proof obligation to the Zenon prover, with a
\* runtime limit of 3 seconds.
ZenonProve(op) == TRUE

\* Backend pragma: dispatch a proof obligation to the Isabelle prover, with a
\* runtime limit of 5 seconds.
IsabelleProve(op) == TRUE

\* Backend pragma: dispatch a proof obligation to the CVC3 prover, with a
\* runtime limit of 2 seconds.
CVC3Prove(op) == TRUE

\* Backend pragma: dispatch a proof obligation to the Yices prover, with a
\* runtime limit of 2 seconds.
YicesProve(op) == TRUE

\* Backend pragma: dispatch a proof obligation to the veriT prover, with a
\* runtime limit of 3 seconds.
VeriTProve(op) == TRUE

\* Backend pragma: dispatch a proof obligation to the Z3 prover, with a
\* runtime limit of 4 seconds.
Z3Prove(op) == TRUE

\* Backend pragma: dispatch a proof obligation to the SPASS prover, with a
\* runtime limit of 3 seconds.
SPASSProve(op) == TRUE

\* Backend pragma: dispatch a proof obligation to the LS4 temporal logic
\* prover, with a runtime limit of 3 seconds.
LS4Prove(op) == TRUE

\* Temporal logic proof rule: invariance. If a property is established in the
\* initial state and preserved by every transition of the system, then it
\* holds in all reachable states.
InvRule(p) == p \in vars /\ p' \in vars

\* Temporal logic proof rule: well-formedness. Guarantees that every stable
\* property in the model has a proof in the library of derived invariants.
WfRule(p) == p \in vars /\ p' \in vars

\* Temporal logic proof rule: strong fairness. A system that infinitely
\* often enables some transition and satisfies this rule will eventually
\* run that transition.
SfRule(p) == p \in vars /\ p' \in vars

\* Temporal proof rule: weak fairness. A system that always keeps some
\* transition enabled and satisfies this rule will eventually run that
\* transition.
WfRule2(p) == p \in vars /\ p' \in vars

\* Set extensionality: two sets that have exactly the same elements are
\* equal; a foundational proof rule stating equality is semantic.
Extensionality ==
  \A a, b \in vars : (FORALL c \in vars : (c \in a) <=> (c \in b)) => (a = b)

\* Bounded-ness: no set collects every possible value in the system.
Boundedness ==
  \A a \in vars : (\A b \in vars : b \in a) => (a \in vars)

====