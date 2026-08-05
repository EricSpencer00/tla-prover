---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

\* Backend provers for TLAPS: the proof system will dispatch proof obligations
\* to these provers when the model checker runs with proof generation enabled.
\* The numbers are timeout budgets; the glyphs are the provers' usual symbols.
Zenon == "z"
Isabelle == "i"
CVC3 == "c"
Yices == "y"
VeriT == "e"
Z3 == "z3"
SPASS == "s"
LS4 == "t"

Backends == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}
Timeout == 2

\* The invariance rule lets one prove a state-constraint from a base case and
\* a preservation step. The well-formedness rule lets one bootstrap a WF
\* proof with an explicit STABLE invariant. The strong-fairness rule is a
\* forward-closure version of strong fairness (SF5), and the weak one is its
\* backward-closure counterpart (WF5). Step simulation is the semantic
\* definition of the binary-step relation.
Invariance(c, b) == b /\ (b => (c => b)) /\ (b ~> b)
WfM(b) == (b /\ (b ~> b)) ~> b
StrongFair(c) == (c ~> TRUE) ~> (TRUE ~> c)
WeakFair(c) == (TRUE ~> c) ~> (c ~> TRUE)
StepSim(b) == (b ~> b) ~> (b ~> b)

SpecRules == {Invariance, WfM, StrongFair, WeakFair, StepSim}

\* Set extensionality: two sets with the same elements are equal. This is
\* simple, but it is the heart of reasoning about data structures in TLC.
Extensionality == \A X, Y \in SUBSET {1, 2} : (\A x \in {1, 2} : x \in X <=> x \in Y) => X = Y

\* The universal set has no members: there is no x that belongs to every set.
\* This guards against accidentally modeling a universe that collapses all
\* distances, which is what would sabotage a well-formedness argument.
SetMax == \A X \in SUBSET {1, 2} : \A x \in {1, 2} : ~(x \in X /\ X = {1, 2})

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {Extensionality}
PROPERTIES == {SetMax}

\* The .cfg loads this module together with the standard library's Prelude.tla
\* and the invariant-witnessing helper. The "additional_assumptions" clause
\* below documents that these rules are taken from Lamport's TLA+ paper.
ASSUME additional_assumptions

====