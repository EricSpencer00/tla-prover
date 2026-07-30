---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

ASSUME D \in Nat /\ N \in 1..4

\* A disk of size k is present on a tower iff the k-th bit of that tower's
\* value is 1.  Because each disk is a distinct power of two, the sum of all
\* tower values always equals 2^D - 1 when no disk is created or destroyed.
\* Towers are indexed 1..N.
Towers == 1..N
Disks == { 2^k : k \in 0..(D - 1) }

RECURSIVE SumOf(_, _)
SumOf(f, S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE
                    IN f[x] + SumOf(f, S \ {x})

\* Bitwise AND, defined arithmetically so no external override is needed.
\* AND(a, b) = 0 iff a and b have no bit in common; otherwise it is non-zero.
AND(a, b) == IF a = 0 \/ b = 0 THEN 0
             ELSE IF a % (2 * (b % 2)) = 0 THEN 0
             ELSE IF a % 2 = 1 /\ b % 2 = 1 THEN 1
             ELSE 2 * AND(a \div 2, b \div 2)

VARIABLES val

vars == <<val>>

TypeOK == /\ val \in [Towers -> 0..(2^D - 1)]

Init ==
  /\ val = [t \in Towers |-> IF t = 1 THEN 2^D - 1 ELSE 0]

\* A move is allowed only if the disk is the smallest on the source tower
\* (no lower bit set on that tower) and the destination tower has no lower
\* disk either (its lower bits are zero), or the destination is empty.
Move(d, s, t) ==
  /\ d \in Disks
  /\ s # t
  /\ AND(val[s], d) = d
  /\ AND(d, val[s] - d) = 0
  /\ (val[t] = 0 \/ AND(d, val[t]) = 0)
  /\ val' = [val EXCEPT ![s] = @ - d, ![t] = @ + d]
  /\ UNCHANGED << >>

Next == \E d \in Disks, s \in Towers, t \in Towers : Move(d, s, t)

Spec == Init /\ [][Next]_vars

Inv == SumOf(val, Towers) = 2^D - 1

====