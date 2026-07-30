---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    TRUE, FALSE

\* backend pragmas for the TLA Proof System: these operators carry no state and
\* never change the model, so every one of them simply returns TRUE. They are
\* nevertheless declared as separate operators because their names are reserved
\* by the proof infrastructure.
Zenon == TRUE
Isabelle == TRUE
CVC3 == TRUE
Yices == TRUE
veriT == TRUE
Z3 == TRUE
SPASS == TRUE
LS4 == TRUE

StateExtensionality ==
    \A s, t \in SUBSET Nat : (\A x \in Nat : (x \in s) <=> (x \in t)) => s = t

NoSetIsUniversal ==
    \A s \in SUBSET Nat : \E y \in Nat : y \notin s

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====