---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

\* Constants required by the original Bakery specification (finite domains)
num      == NatOverride
max      == NatOverride
pc       == {"idle", "wait", "critical"}
unchecked == {}
nxt      == {}
flag     == {"true", "false"}

\* Include the original Bakery specification
INSTANCE Bakery

\* Inductive specification: start from any type‑correct state and enforce the next‑state relation forever
ISpec == TypeOK /\ [][Next]_vars

====