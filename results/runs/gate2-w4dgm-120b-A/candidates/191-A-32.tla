---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

Towers == 0 .. (N - 1)
NULLDISK == 0

VARIABLES tower

vars == <<tower>>

Bits == { 2 ^ k : k \in 0 .. (D - 1) }

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + SumOf(f, S \ {x})

\* Bitwise AND (custom operator; no built-in support in pure TLA+): a & b is the
\* sum of those powers-of-two that divide both a and b.
BitwiseAnd(a, b) ==
  LET f[x] == IF x \in Bits /\ x <= a /\ x <= b THEN x ELSE 0
  IN SumOf(f, Bits)

Init ==
  /\ tower \in [Towers -> 0 .. (2 ^ D - 1)]
  /\ tower[0] = 2 ^ D - 1
  /\ \A t \in Towers \ {0} : tower[t] = NULLDISK

\* The disk must be present on the source tower and be the smallest there; the
\* destination must be empty or hold only larger disks, and the disk is taken
\* off the source and dropped onto the destination.
Move(disk, src, dst) ==
  /\ src # dst
  /\ tower[src] >= disk
  /\ BitwiseAnd(tower[src], disk) = disk
  /\ \A k \in 0 .. (D - 1) : (2 ^ k) < disk => (BitwiseAnd(tower[src], 2 ^ k) = NULLDISK)
  /\ \A k \in 0 .. (D - 1) : (2 ^ k) < disk => (BitwiseAnd(tower[dst], 2 ^ k) = NULLDISK)
  /\ tower' = [tower EXCEPT ![src] = @ - disk, ![dst] = @ + disk]

Next ==
  \E disk \in 1 .. (2 ^ D - 1), src, dst \in Towers : Move(disk, src, dst)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ tower \in [Towers -> 0 .. (2 ^ D - 1)]

\* Nothing is created or destroyed: the sum of tower values is always the full
\* stack weight 2^D - 1.
Inv == SumOf(tower, Towers) = 2 ^ D - 1

====