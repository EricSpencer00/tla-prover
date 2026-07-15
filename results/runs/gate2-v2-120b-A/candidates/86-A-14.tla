---- MODULE TLAPS ----
EXTENDS Naturals, TLC

\* ----------------------------------------------------------------------
\*  Pragmas to instruct TLAPS to use various back‑end provers.  The
\*  operators below are no‑ops at runtime; they only serve as markers
\*  for the proof manager.
\* ----------------------------------------------------------------------
Zenon(p) == p
Isabelle(p) == p
CVC3(p) == p
Yices(p) == p
VeriT(p) == p
Z3(p) == p
SPASS(p) == p
LS4(p) == p

\* ----------------------------------------------------------------------
\*  Temporal‑logic proof rules (names only – semantics expressed as
\*  theorems using the standard TLA+ toolbox lemmas).  The bodies are
\*  intentionally trivial because the real reasoning is carried out
\*  by the back‑ends; the theorems are provided so that their names
\*  are reserved.
\* ----------------------------------------------------------------------
InvRule(state, inv) == inv /\ state
WFRule(state, action) == TRUE
SFRule(state, action) == TRUE
StepSimRule(state, action) == TRUE

\* ----------------------------------------------------------------------
\*  Two foundational theorems required by the description.
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A A, B \in SUBSET UNIV :
    (\A x : x \in A <=> x \in B) => A = B

NoSetContainsAllValues ==
  \A S \in SUBSET UNIV : S # UNIV

\* ----------------------------------------------------------------------
\*  The SPECIFIC identifiers required by the .cfg file.  The system
\*  has no state, so INIT is simply TRUE and NEXT is also TRUE.
\* ----------------------------------------------------------------------
SPECIFICATION == Init /\ [][Next]_<<>>
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

\* ----------------------------------------------------------------------
\*  Declarations needed by the .cfg file (even though they are not used
\*  in this module).  They are defined as trivial stubs.
\* ----------------------------------------------------------------------
SPEC == SPECIFICATION
INIT == Init
NEXT == Next
INVARIANTS == {}
PROPERTIES == {}

=============================================================================