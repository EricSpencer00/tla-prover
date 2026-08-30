---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

Bits == 0 .. (D - 1)
Towers == 1 .. N
DiskSize(k) == 2 ^ k
TotalSize == 2 ^ D - 1

VARIABLES tower
vars == <<tower>>

RECURSIVE SumTowers(_)
SumTowers(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE e \in S : TRUE IN tower[x] + SumTowers(S \ {x})

TypeOK ==
  /\ tower \in [Towers -> 0 .. TotalSize]
  /\ SumTowers(Towers) = TotalSize

Init ==
  /\ tower = [t \in Towers |-> IF t = 1 THEN TotalSize ELSE 0]

\* Bit k of a number is on iff the remainder mod 2^(k+1) is at least 2^k.
BitOn(num, k) == ((num % (2 ^ (k + 1))) >= 2 ^ k)

Move(d, src, dst) ==
  /\ src # dst
  /\ BitOn(tower[src], d)
  /\ \A k \in Bits : BitOn(tower[src], k) => k >= d
  /\ \A k \in Bits : BitOn(tower[dst], k) => k > d
  /\ tower' = [tower EXCEPT ![src] = @ - DiskSize(d), ![dst] = @ + DiskSize(d)]

Next ==
  \E d \in Bits, src, dst \in Towers : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

Inv == SumTowers(Towers) = TotalSize
====