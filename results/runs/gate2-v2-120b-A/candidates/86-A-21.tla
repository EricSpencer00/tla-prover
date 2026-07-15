---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(* --====================================================================--
   TLAPS: Backend pragmas for the TLA Proof System
   This module defines operators that direct TLAPS to use various
   automated provers and encodes fundamental temporal‑logic proof rules.
   No state variables are needed for the configuration; the operators are
   pure functions used only by the proof manager.
   --====================================================================-- *)

\* ----------------------------------------------------------------------
\* Backend prover configuration operators
\* (These operators are placeholders; their semantics are interpreted by TLAPS)
\* ----------------------------------------------------------------------
Zenon(timeout) == timeout
Isabelle(timeout) == timeout
CVC3(timeout) == timeout
Yices(timeout) == timeout
veriT(timeout) == timeout
Z3(timeout) == timeout
SPASS(timeout) == timeout
LS4(timeout) == timeout

\* ----------------------------------------------------------------------
\* Fundamental temporal‑logic proof rules (names reserved for future use)
\* ----------------------------------------------------------------------
\* Invariance rule
InvRule(Inv, Init, Next) ==
    /\ \A s \in Init : Inv(s)
    /\ \A s, s' \in Nat :
        /\ s \in Inv
        /\ Next(s, s')
        => s' \in Inv

\* Well‑formedness rules (placeholder definitions)
WFRule_Actions(actions) == TRUE
WFRule_Stuttering(stutter) == TRUE

\* Strong fairness rule
StrongFairness(Fair, Init, Next) ==
    /\ \A s \in Nat : Init(s) => \E i \in Nat : Fair(i) /\ Next(s, i)

\* Weak fairness rule
WeakFairness(Fair, Init, Next) ==
    /\ \A s \in Nat :
        Init(s) /\ \A i \in Nat : ~Fair(i) => Next(s, i)

\* Step simulation rule
StepSim(SrcInit, SrcNext, TgtInit, TgtNext, Sim) ==
    /\ \A s \in Nat : SrcInit(s) => TgtInit(Sim(s))
    /\ \A s, s' \in Nat :
        /\ SrcNext(s, s')
        => TgtNext(Sim(s), Sim(s'))

\* ----------------------------------------------------------------------
\* Safety theorems
\* ----------------------------------------------------------------------
SetExtensionality ==
    \A A, B \in SUBSET Nat :
        (\A x \in Nat : x \in A <=> x \in B) => A = B

NoUniversalSet ==
    \A x \in Nat : x \notin { y \in Nat : TRUE }

=============================================================================