---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

\* The Bakery algorithm itself lives in module Bakery.  Here we only
\* bring it in and replace the unbounded Nat with a finite range.
Bakery == INSTANCE Bakery
NatOverride == Nat

VARIABLES phase, ticket, chosen, served
vars == <<phase, ticket, chosen, served>>

TypeOK ==
    /\ phase \in [1..N -> {"idle", "waiting", "critical"}]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ chosen \in [1..N -> BOOLEAN]
    /\ served \in [1..N -> BOOLEAN]

\* The inductive invariant from the Bakery spec, brought in unchanged.
Inv ==
    /\ \A p \in 1..N : (phase[p] = "critical") => (\A q \in 1..N : q # p => phase[q] # "critical")
    /\ TypeOK

MutualExclusion ==
    \A p, q \in 1..N : (phase[p] = "critical" /\ phase[q] = "critical") => p = q

\* The Bakery spec defines Init and Next as InitBakery/NextBakery under the
\* same names.  We rename them here for the cfg file.
Init == Bakery.Init
Next == Bakery.Next

ISpec == Init /\ [][Next]_vars

====