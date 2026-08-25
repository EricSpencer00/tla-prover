---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\* ----------------------------------------------------------------------
\* Finite replacement for the infinite set of natural numbers.
\* The model‑checking configuration overrides the usual Nat with this
\* bounded range.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* Specification used by the .cfg file.
\* Bakery already defines the standard specification as `Spec`.  We expose
\* it under the name required by the configuration.
\* ----------------------------------------------------------------------
ISpec == Spec

\* ----------------------------------------------------------------------
\* Type correctness invariant.
\* All variables must stay within their intended domains, with the ticket
\* numbers drawn from the finite NatOverride range.
\* ----------------------------------------------------------------------
TypeOK == 
  /\ pc \in [1..N -> {"idle","wait","cs","exit"}]
  /\ flag \in [1..N -> BOOLEAN]
  /\ label \in [1..N -> NatOverride]

\* ----------------------------------------------------------------------
\* Mutual‑exclusion safety property.
\* No two distinct processes may be in the critical section simultaneously.
\* ----------------------------------------------------------------------
MutualExclusion == 
  \A i, j \in 1..N : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

\* ----------------------------------------------------------------------
\* Full inductive invariant required by the configuration.
\* It combines type correctness, the ordering property of the bakery
\* tickets, and the mutual‑exclusion guarantee.
\* ----------------------------------------------------------------------
Inv ==
  /\ TypeOK
  /\ \A i \in 1..N :
        /\ pc[i] = "cs" => 
             \A j \in 1..N : (j # i) => pc[j] # "cs"
        /\ flag[i] => 
             \A j \in 1..N :
               /\ flag[j]
               /\ (label[j] < label[i] \/ (label[j] = label[i] /\ j < i))
               => pc[j] = "cs"

====