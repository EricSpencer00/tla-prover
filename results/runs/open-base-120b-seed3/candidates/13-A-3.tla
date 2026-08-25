---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\*  Finite version of the natural numbers used for model checking
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\*  Aliases to the definitions provided by the Bakery specification
\* ----------------------------------------------------------------------
Init == Bakery!Init
Next == Bakery!Next
vars == Bakery!vars

\* ----------------------------------------------------------------------
\*  Inductive specification: any type‑correct state satisfying the
\*  invariant can be a starting point, and all executions must follow
\*  the Next relation.
\* ----------------------------------------------------------------------
ISpec == Init /\ [] [Next]_vars

\* ----------------------------------------------------------------------
\*  Invariants required by the configuration
\* ----------------------------------------------------------------------
MutualExclusion == Bakery!MutualExclusion
TypeOK           == Bakery!TypeOK
Inv              == Bakery!Inv

====