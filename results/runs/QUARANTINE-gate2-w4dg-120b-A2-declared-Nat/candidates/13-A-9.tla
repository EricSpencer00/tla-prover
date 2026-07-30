---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

RECURSIVE MaxNat_(_)
MaxNat_(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN IF x > MaxNat_(S \ {x}) THEN x ELSE MaxNat_(S \ {x})

\* NatOverride is what the .cfg file substitutes over the built-in Nat, and
\* it must be defined here with this exact name for the substitution to work.
NatOverride == 0 .. MaxNat

\* Inherit the Bakery specification under the name the .cfg expects.  The
\* action set is unchanged; only the ticket bounds are reduced here.
BakerySpec(N, NatOverride) == INSTANCE Bakery WITH N == N, Nat == NatOverride

Spec == BakerySpec(N, NatOverride).Spec
ISpec == BakerySpec(N, NatOverride).Spec

Init == BakerySpec(N, NatOverride).Init
Next == BakerySpec(N, NatOverride).Next

MutualExclusion == BakerySpec(N, NatOverride).MutualExclusion
TypeOK == BakerySpec(N, NatOverride).TypeOK
Inv == BakerySpec(N, NatOverride).Inv

====