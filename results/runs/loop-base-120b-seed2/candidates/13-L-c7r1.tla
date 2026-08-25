---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

\* Tuple of the state variables defined in the Bakery specification
vars == <<pc, number, flag>>

\* Type correctness invariant
TypeOK ==
  /\ pc \in [1..N -> {"idle", "wait", "cs"}]
  /\ number \in [1..N -> NatOverride]
  /\ flag \in [1..N -> BOOLEAN]

\* Mutual exclusion invariant
MutualExclusion ==
  \A i, j \in 1..N : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

\* Overall invariant
Inv == TypeOK /\ MutualExclusion

\* Inductive specification: any state satisfying the invariant is a legal start,
\* and all steps must follow the Next action of the Bakery algorithm.
ISpec == Inv /\ [][Next]_vars

====