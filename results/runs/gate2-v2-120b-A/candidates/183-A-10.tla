---- MODULE TLAPS ----
EXTENDS Naturals, Reals, Sequences, TLC

\* ==============================================================
\* Configuration constants controlling TLAPS back‑ends.
\* (No required identifiers are listed in the .cfg, but we expose
\*  the typical set of configuration constants for completeness.)
\* ==============================================================

CONSTANTS
    ZenonTimeout, IsabelleTimeout, CVC3Timeout,
    YicesTimeout, VeritTimeout, Z3Timeout,
    SPASSTimeout, LS4Timeout,
    ZenonOptions, IsabelleOptions, CVC3Options,
    YicesOptions, VeritOptions, Z3Options,
    SPASSOptions, LS4Options,
    ZenonTactics, IsabelleTactics, CVC3Tactics,
    YicesTactics, VeritTactics, Z3Tactics,
    SPASSTactics, LS4Tactics

\* ==============================================================
\* TLAPS backend directives (modelled as simple operators).
\* In an actual proof these would be pragma-like commands; here we
\* merely make their names available so the TLC model checker can
\* see that they exist.
\* ==============================================================

Zenon(timeout)      == timeout
Isabelle(timeout)   == timeout
CVC3(timeout)       == timeout
Yices(timeout)      == timeout
Verit(timeout)      == timeout
Z3(timeout)         == timeout
SPASS(timeout)      == timeout
LS4(timeout)        == timeout

\* ==============================================================
\* Temporal‑logic proof‑rule placeholders.
\* These operators stand for theorems in the underlying proof
\* library.  They are defined as stubs that always return TRUE.
\* ==============================================================

\* Invariance rule
InvRule(Inv) == TRUE

\* Strong fairness rule
StrongFairness(Pred) == TRUE

\* Weak fairness rule
WeakFairness(Pred) == TRUE

\* Well‑formedness rule (e.g., type correctness)
WellFormed(Expr) == TRUE

\* Step‑simulation rule
StepSim(Prev, Next) == TRUE

\* ==============================================================
\* Fundamental theorems required by the description.
\* ==============================================================

SetExtensionality ==
    \A A, B \in SUBSET UNIV :
        (\A x : x \in A <=> x \in B) => A = B

NoSetHasAllValues ==
    \A S \in SUBSET UNIV :
        \A x \in UNIV : x \in S => FALSE

\* ==============================================================
\* (No state variables or actions are specified for this module.)
\* We therefore define a trivial state and a trivial specification.
\* ==============================================================

VARIABLE dummy

Init == dummy = 0

Next == /\ dummy' = dummy
        /\ UNCHANGED dummy

Spec == Init /\ [][Next]_<<dummy>>

\* ==============================================================

====