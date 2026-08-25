---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* ---------- Finite natural numbers for model checking ----------
NatOverride == 0 .. MaxNat

\* ---------- Variables ----------
VARIABLE n

\* ---------- Helper definition ----------
Even(x) == \E k \in NatOverride : x = 2 * k

\* ---------- Initialization ----------
INIT == n \in NatOverride

\* ---------- Next-state relation ----------
NEXT == UNCHANGED n

\* ---------- Specification ----------
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

\* ---------- Invariant that should always hold ----------
INVARIANTS == Even(2 * n)

\* ---------- Property to be checked (the theorem) ----------
PROPERTIES == \A m \in NatOverride : Even(2 * m)
====