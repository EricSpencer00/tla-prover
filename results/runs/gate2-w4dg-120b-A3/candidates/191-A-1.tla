---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values: each tower's value is the binary sum of the size-values of
\* the disks currently standing on it. The disk values are powers of two, so
\* each tower's value is a bitmask. A stack is never reordered, only moved.
\* Every move therefore moves exactly one set bit from one tower to another.
Towers == [1..N -> 0..(2 ^ D - 1)]

RECURSIVE SumF(_, _)
SumF(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + SumF(f, S \ {x})

VARIABLES tower

vars == <<tower>>

\* A tower holds the stack only if it has no disk smaller than the one
\* being moved: no lower-order bits are set in the destination tower.
HasNoSmaller(t, d) == (t # 0) => ((t % (2 * d)) \in {0, d})
Smallest(t, d) == d <= t /\ (t % (2 * d)) = d

TypeOK ==
  /\ tower \in Towers
  /\ tower[1] # 0
  /\ SumF(tower, 1..N) = 2 ^ D - 1

\* The entire sum of all towers must stay at 2^D - 1: bits are only ever
\* moved between towers, never created or destroyed.
Inv == SumF(tower, 1..N) = 2 ^ D - 1

Init ==
  /\ tower = [t \in 1..N |-> IF t = 1 THEN 2 ^ D - 1 ELSE 0]
  /\ UNCHANGED tower

\* A single move: move one smallest-disk-from-a-stack onto a tower that has
\* no smaller disk already standing there.
Move(d, src, dst) ==
  /\ src # dst
  /\ d >= 1 /\ d <= 2 ^ (D - 1)
  /\ d \in {2 ^ k : k \in 0..(D - 1)}
  /\ (tower[src] % (2 * d)) = d
  /\ HasNoSmaller(tower[dst], d)
  /\ tower' = [tower EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \/ \E d \in {2 ^ k : k \in 0..(D - 1)}:
       \E src \in 1..N: \E dst \in 1..N: Move(d, src, dst)

Spec ==
  /\ Init
  /\ [][Next]_vars

====