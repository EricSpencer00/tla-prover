---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(*  TLAPS:  Backend pragmas and temporal logic proof rules for TLAPS.       *)
(*  This module provides operators that specify which back‑end provers     *)
(*  (Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4) to use, as well  *)
(*  as fundamental temporal‑logic theorems (invariance, fairness, etc.).   *)
(***************************************************************************)

\* ----------------------------------------------------------------------
\* Configuration constants (not used in the state, but declared for TLC)
\* ----------------------------------------------------------------------
CONSTANTS
    ZenonTimeout,
    IsabelleTimeout,
    Cvc3Timeout,
    YicesTimeout,
    VeriTTimeout,
    Z3Timeout,
    SpassTimeout,
    Ls4Timeout

\* ----------------------------------------------------------------------
\* State variable
\* ----------------------------------------------------------------------
VARIABLES dummy

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    dummy \in {0}

\* ----------------------------------------------------------------------
\* Stutter step (the system does not change state)
\* ----------------------------------------------------------------------
Next ==
    UNCHANGED dummy

\* ----------------------------------------------------------------------
\* Specification (the behavior of the system)
\* ----------------------------------------------------------------------
SPECIFICATION ==
    Init /\ [][Next]_<<dummy>>

\* ----------------------------------------------------------------------
\* Backend‑selection operators
\* ----------------------------------------------------------------------
Zenon == TRUE               \* placeholder – selects Zenon as a prover
Isabelle == TRUE            \* placeholder – selects Isabelle
Cvc3 == TRUE                \* placeholder – selects CVC3
Yices == TRUE               \* placeholder – selects Yices
VeriT == TRUE               \* placeholder – selects veriT
Z3 == TRUE                  \* placeholder – selects Z3
Spass == TRUE               \* placeholder – selects SPASS
Ls4 == TRUE                 \* placeholder – selects LS4

\* ----------------------------------------------------------------------
\* Temporal‑logic proof‑rule operators (names reserved for later use)
\* ----------------------------------------------------------------------
InvRule(P) ==  []P
WFRule(P) == WF_dummy(P)      \* weak fairness on the dummy variable
SFRule(P) == SF_dummy(P)      \* strong fairness on the dummy variable
StepSim(P, Q) == [] (P => <>Q) \* step‑simulation rule (illustrative)

\* ----------------------------------------------------------------------
\* Fundamental theorems required by the description
\* ----------------------------------------------------------------------
SetExtensionality ==
    \A A, B : ( \A x : x \in A <=> x \in B ) => A = B

NoSetContainsAll ==
    \A A : \E x : x \notin A

\* ----------------------------------------------------------------------
\* Operators required by the .cfg (none are explicitly listed, but we
\* define the standard ones for completeness)
\* ----------------------------------------------------------------------
INVARIANTS == {}
PROPERTIES == {}

\* ----------------------------------------------------------------------
\* The module ends with the standard TLA+ footer.
\* ----------------------------------------------------------------------
====