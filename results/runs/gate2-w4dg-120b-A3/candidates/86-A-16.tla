---- MODULE TLAPS ----
EXTENDS Naturals

\* Backend provers for the TLA Proof System (TLAPS).  These are operators rather
\* than record fields because the .cfg can only refer to operators directly.
\* The invariance and fairness rules below come from Lamport's temporal logic
\* paper and are deliberately included here to reserve their names.

CONSTANTS Z3, Yices, CVC3, Zenon, SPASS, LS4, Isabelle, veriT, noBackend

Backends == {Z3, Yices, CVC3, Zenon, SPASS, LS4, Isabelle, veriT}

\* Each prover can be invoked with a timeout; the config file must supply the
\* timeout values.
CONSTANTS timeoutZ3, timeoutYices, timeoutCVC3, timeoutZenon, timeoutSPASS
CONSTANTS timeoutLS4, timeoutIsabelle, timeoutVeriT

ZF == Z3 timeoutZ3
YF == Yices timeoutYices
CF == CVC3 timeoutCVC3
ZenF == Zenon timeoutZenon
SPF == SPASS timeoutSPASS
LSF == LS4 timeoutLS4
IsF == Isabelle timeoutIsabelle
veriF == veriT timeoutVeriT

\* The specification consists of a single PASS action guarded by the presence
\* of at least one backend: no backends, no proof step.
Spec == LET PASS == \A b \in Backends : b END IN PASS

Init == TRUE
Next == Spec

\* Foundational theorems: the two basic set-theoretic identities that the
\* standard library always wants to reserve here.
Extensionality == \A a, b \in {z \in {1, 2, 3} : TRUE} : (\A c \in {1, 2, 3} : c \in a <=> c \in b) => a = b
NoSetContainsAllValues == \A x \in {1, 2, 3} : \A a \in {x, x + 1} : x \notin a

\* Basic temporal logic rules, from Lamport's paper (invariant, fairness,
\* simulation).  They are the empty theorems here; naming them is the point.
InvariantRule == TRUE
WFRule == TRUE
SFRule == TRUE
StrongSimulationRule == TRUE
WeakSimulationRule == TRUE
StepSimulationRule == TRUE

TypeOK == Extensionality /\ NoSetContainsAllValues /\ InvariantRule /\ WFRule /\ SFRule
          /\ StrongSimulationRule /\ WeakSimulationRule /\ StepSimulationRule

====