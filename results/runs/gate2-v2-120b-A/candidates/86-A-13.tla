---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* -----------------------------------------------------------------
\* Constants (none specified in the natural-language description)
\* -----------------------------------------------------------------
CONSTANTS

\* -----------------------------------------------------------------
\* State variables (none specified)
\* -----------------------------------------------------------------
VARIABLES

\* -----------------------------------------------------------------
\* Operators that represent backend prover directives for TLAPS
\* (they are defined as no‑ops in the model; the proof system interprets
\*  them when a proof is checked)
\* -----------------------------------------------------------------
Zenon(e) == e
Isabelle(e) == e
CVC3(e) == e
Yices(e) == e
VeriT(e) == e
Z3(e) == e
SPASS(e) == e
LS4(e) == e

\* Optional timeout and tactic annotations (also no‑ops)
Timeout(e, t) == e
Tactic(e, tac) == e

\* -----------------------------------------------------------------
\* Temporal‑logic proof rule placeholders
\* (they are defined as implications that are trivially true; the
\*  actual rules are provided by the proof system)
\* -----------------------------------------------------------------
InvRule(Inv, Init, Next) == Inv /\ [][Next]_<<>> => []Inv
WFRule(Fair, Init, Next) == WF(Fair) => [][Next]_<<>>
SFRule(Fair, Init, Next) == SF(Fair) => [][Next]_<<>>
StepSimRule(Spec, Sim) == Spec => Sim

\* -----------------------------------------------------------------
\* Set‑extensionality theorem (axiom) and the “no universal set” theorem
\* -----------------------------------------------------------------
SetExt(A, B) == \A x : (x \in A) = (x \in B) => A = B
NoUniversalSet == \A S : ~ (UNIV \subseteq S)

\* -----------------------------------------------------------------
\* Specification (no actions or state, so the SPEC is simply TRUE)
\* -----------------------------------------------------------------
Spec == TRUE

Init == Spec
Next == Spec

SPECIFICATION == Spec

\* -----------------------------------------------------------------
\* Safety theorems required by the description
\* -----------------------------------------------------------------
SetExtensionality == SetExt({1,2}, {1,2})
NoSetContainsAll == NoUniversalSet

INVARIANTS == { SetExtensionality, NoSetContainsAll }

PROPERTIES == {}

=============================================================================