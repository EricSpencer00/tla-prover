---- MODULE MCBakery ----
EXTENDS Bakery
CONSTANT MaxNat
RECURSIVE NatOverride(_)
NatOverride(n) == IF n = 0 THEN {0} ELSE NatOverride(n-1) \cup {n}
=============================================================================