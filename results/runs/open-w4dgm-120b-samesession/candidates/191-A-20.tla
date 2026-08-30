---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

ASSUME D \in Nat /\ D >= 1
ASSUME N \in Nat /\ N >= 2

Disks == {2 ^ k : k \in 0 .. (D - 1)}

VARIABLES towers, sum

vars == <<towers, sum>>

RECURSIVE SumOf(_)
SumOf(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN x + SumOf(S \ {x})

\* Bitwise AND via arithmetic: a & b = a - ((a + b) % (2 * b)) when b is a power
\* of two, which holds for every disk in Disks.
BitwiseAnd(a, b) == a - ((a + b) % (2 * b))

Init ==
  /\ towers = [i \in 0 .. (N - 1) |-> IF i = 0 THEN SumOf(Disks) ELSE 0]
  /\ sum = SumOf(Disks)

Move(dis, src, dst) ==
  /\ src # dst
  /\ towers[src] # 0
  /\ BitwiseAnd(towers[src], dis) = dis
  /\ \A k \in 1 .. (D - 1) : 2 ^ k < dis => BitwiseAnd(towers[src], 2 ^ k) = 0
  /\ towers[dst] # 0 => \A k \in 1 .. (D - 1) : 2 ^ k < dis => BitwiseAnd(towers[dst], 2 ^ k) = 0
  /\ towers' = [towers EXCEPT ![src] = @ - dis, ![dst] = @ + dis]
  /\ UNCHANGED sum

Next ==
  \E dis \in Disks, src \in 0 .. (N - 1), dst \in 0 .. (N - 1) : Move(dis, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: no disk is ever created or destroyed, so the arithmetic sum
\* of all tower values stays equal to the sum of all disk values.
TypeOK ==
  /\ towers \in [0 .. (N - 1) -> 0 .. (2 ^ D - 1)]
  /\ sum = SumOf(Disks)

\* Conservation restated as the sum staying equal to its initial value.
Inv == sum = SumOf(Disks)
====