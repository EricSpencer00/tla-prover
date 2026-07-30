---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower state is encoded as the sum of present disk values, where each
\* disk is a power of two. Bitwise AND (implemented below) tests presence.
VARIABLES towers

vars == << towers >>

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

\* The sum of all tower values always equals 2^D - 1: conservation.
Sum == SumOver(towers, 1..N)

Disk(k) == 2 ^ k
Disks == { Disk(k) : k \in 1..D }

On(t, d) == (towers[t] / d) % 2 = 1

\* Smallest disk on a tower: all smaller bits are zero, so the remainder
\* of t mod (2 * d) equals exactly d.
SmallestOn(t, d) == towers[t] % (2 * d) = d

\* Destination has no smaller disk: remainder of t mod (2 * d) is zero.
DestFree(t, d) == towers[t] % (2 * d) = 0

Init ==
  /\ towers = [t \in 1..N |-> IF t = 1 THEN 2 ^ D - 1 ELSE 0]
  /\ Sum = 2 ^ D - 1

\* A single legal move: remove a smallest disk from a source tower and
\* add it to a destination tower that has no smaller disk.
Move(d, s, dst) ==
  /\ s # dst
  /\ On(s, d)
  /\ SmallestOn(s, d)
  /\ DestFree(dst, d)
  /\ towers' = [towers EXCEPT ![s] = @ - d, ![dst] = @ + d]
  /\ UNCHANGED Sum

Next == \E d \in Disks, s, dst \in 1..N : Move(d, s, dst)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ towers \in [1..N -> 0..(2 ^ D - 1)]
  /\ Sum = 2 ^ D - 1

Inv == Sum = 2 ^ D - 1

====