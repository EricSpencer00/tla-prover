---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* -------------------------------------------------
\* Backend provers configuration (TLAPS pragmas)
\* -------------------------------------------------
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4
CONSTANTS ZenonTimeout, IsabelleTimeout, CVC3Timeout, YicesTimeout,
          VeriTTimeout, Z3Timeout, SPASSTimeout, LS4Timeout

\* Pragmas used by TLAPS.  The bodies are trivial because they are
\* interpreted only by the proof manager, not by the model checker.
ZenonBackend(expr) == TRUE
IsabelleBackend(expr) == TRUE
CVC3Backend(expr) == TRUE
YicesBackend(expr) == TRUE
VeriTBackend(expr) == TRUE
Z3Backend(expr) == TRUE
SPASSBackend(expr) == TRUE
LS4Backend(expr) == TRUE

\* -------------------------------------------------
\* Fundamental set‑theoretic theorems
\* -------------------------------------------------
THEOREM SetExtensionality ==
  \A A, B \in SUBSET UNIV :
    ( \A x \in A : x \in B ) /\ ( \A x \in B : x \in A ) => A = B

THEOREM NoUniversalSet ==
  ~\E S \in SUBSET UNIV : \A x : x \in S

\* -------------------------------------------------
\* Temporal‑logic proof‑rule placeholders (names reserved)
\* -------------------------------------------------
InvRule(P, Init, Next) == TRUE      \* invariance rule
WFRule(P) == TRUE                    \* well‑formedness rule
SFRule(P) == TRUE                    \* strong fairness rule
WFRule(P) == TRUE                    \* weak fairness rule
StepSimRule(Init, Next) == TRUE      \* step‑simulation rule

\* -------------------------------------------------
\* Minimal specification skeleton (no state variables)
\* -------------------------------------------------
Init == TRUE
Next == TRUE

SPECIFICATION == Init /\ [][Next]_<<>>

INVARIANTS == {}
PROPERTIES == {}

====