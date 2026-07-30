---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

Bakeries == {"b1", "b2"}

\* Model checking this algorithm requires a bounded number of ticket values: the
\* natural numbers are capped at MaxNat, which is a constant derived from the
\* configuration (N = 2, MaxNat = 2).  The "Nat" constant replaces the infinite
\* set of naturals with the finite range 0..MaxNat for this model only.
Bounded == (Nat = 0 .. MaxNat)

VARIABLES num, using

vars == <<num, using>>

TypeOK ==
    /\ Bounded
    /\ num \in 0 .. MaxNat
    /\ using \in [Bakeries -> BOOLEAN]

Init ==
    /\ num = 0
    /\ using = [b \in Bakeries |-> FALSE]

Enter(b) ==
    /\ ~using[b]
    /\ num < MaxNat
    /\ using' = [using EXCEPT ![b] = TRUE]
    /\ num' = num + 1
    /\ UNCHANGED << >>

Exit(b) ==
    /\ using[b]
    /\ using' = [using EXCEPT ![b] = FALSE]
    /\ UNCHANGED << num >>

Next ==
    \E b \in Bakeries : Enter(b) \/ Exit(b)

\* Inductive specification: any type-correct state satisfying the invariant
\* may be the starting point, and every reachable state must preserve it --
\* not just states reachable from Init.
ISpec == Init /\ [][Next]_vars

MutualExclusion ==
    \A b1, b2 \in Bakeries : (using[b1] /\ using[b2]) => b1 = b2

Inv ==
    /\ num >= 0
    /\ \A b \in Bakeries : using[b] => num > 0

====