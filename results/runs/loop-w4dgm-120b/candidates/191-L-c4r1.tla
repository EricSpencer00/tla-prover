---- MODULE Hanoi ----
EXTENDS Integers, FiniteSets

CONSTANTS D, N

\* Each tower's value is a natural number encoding which disks sit there:
\* the k-th bit (value 2^k) is set iff the disk of size 2^k is present.
\* Conservation is therefore a bitwise partition of the number 2^D - 1.
Towers == 1..N
MaxVal == 2^D - 1

\* Bitwise AND via arithmetic: a & b = 0 iff no power of two divides both.
AND(a, b) == IF \E k \in 1..D : (2^(k - 1)) % a = 0 /\ (2^(k - 1)) % b = 0
             THEN 0 ELSE 1

VARIABLES tval

vars == <<tval>>

\* Sum of all tower values; equal to the tally of every disk's size.
SumT == LET f[S \in SUBSET Towers] ==
            IF S = {} THEN 0
            ELSE LET x == CHOOSE y \in S : TRUE IN tval[x] + f[S \ {x}]
        IN f[Towers]

Init ==
    /\ tval = [t \in Towers |-> IF t = 1 THEN MaxVal ELSE 0]
    /\ UNCHANGED << >>

\* A move is valid only if the disk is the smallest on its source tower
\* (nothing smaller is present there) and the destination has no smaller
\* disk either; the disk values move, nothing is created or destroyed.
Move(d, src, dst) ==
    /\ src # dst
    /\ d <= tval[src]
    /\ AND(d, tval[src] - d) = 0
    /\ AND(d, tval[dst]) = 0
    /\ tval' = [tval EXCEPT ![src] = tval[src] - d, ![dst] = tval[dst] + d]
    /\ UNCHANGED << >>

Next ==
    \E d \in { 2^(k - 1) : k \in 1..D } : \E src \in Towers : \E dst \in Towers : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ tval \in [Towers -> 0..MaxVal]
    /\ SumT <= MaxVal

\* Conservation of the bitwise partition: the bits across all towers
\* always account for exactly the full set of disks (no loss, no gain).
Inv ==
    /\ SumT = MaxVal
    /\ \A t \in Towers : tval[t] >= 0

====