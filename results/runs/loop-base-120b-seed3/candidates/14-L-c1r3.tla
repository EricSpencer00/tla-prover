---- MODULE MCBoulanger ----
EXTENDS Naturals
CONSTANTS N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* Definitions needed to instantiate the Boulanger specification
num == 1 .. N
max == MaxNat
pc == {"idle", "request", "critical", "exit"}
previous == [i \in num |-> IF i = 1 THEN N ELSE i - 1]
nxt == [i \in num |-> IF i = N THEN 1 ELSE i + 1]
flag == [i \in num |-> FALSE]
unchecked == {}

\* Bring in the full Boulanger specification under the name B
INSTANCE Boulanger AS B

\* Export the required identifiers for the .cfg file
Spec == B!Spec
MutualExclusion == B!MutualExclusion
TypeOK == B!TypeOK
Inv == B!Inv
====