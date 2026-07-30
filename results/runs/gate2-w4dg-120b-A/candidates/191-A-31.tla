---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Disk sizes are powers of two: 1, 2, 4, ..., 2^(D-1). A tower's value is the
\* sum of the disks on it, so its binary representation encodes exactly which
\* disks are present (bit k set iff disk of size 2^k is on the tower).
\* Disk presence / ordering tests use bitwise AND.

VARIABLES towers

vars == <<towers>>

Towers == 1 .. N
Disks == { 2 ^ k : k \in 0 .. (D - 1) }

RECURSIVE SumOf(_)
SumOf(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN x + SumOf(S \ {x})

TypeOK ==
  /\ towers \in [Towers -> 0 .. (2 ^ D) - 1]
  /\ SumOf({ towers[i] : i \in Towers }) = (2 ^ D) - 1

\* A disk is the smallest on its tower if no smaller disk (lower bit) is set.
SmallestOn(t, d) ==
  /\ (towers[t] & (d - 1)) = 0
  /\ (towers[t] & d) = d

Init ==
  /\ towers = [i \in Towers |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

Move ==
  \E d \in Disks, src \in Towers, dst \in Towers :
    /\ src # dst
    /\ (towers[src] & d) = d
    /\ SmallestOn(src, d)
    /\ (towers[dst] = 0 \/ SmallestOn(dst, d))
    /\ towers' = [towers EXCEPT ![src] = towers[src] - d, ![dst] = towers[dst] + d]

Next == Move

Spec == Init /\ [][Next]_vars

Inv == TypeOK
====