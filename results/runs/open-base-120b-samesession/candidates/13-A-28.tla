---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* Aliases for the actions defined in the Bakery module
INIT == Init
NEXT == Next

\* The tuple of state variables (as defined in Bakery)
Vars == <<pc, ticket, choosing>>

\* The specification to be checked by TLC
ISpec == Init /\ [][Next]_Vars

====