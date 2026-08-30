---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower state is the sum of present disk values (powers of two), so a bitwise
\* AND test on a tower value determines which disks are on it and their ordering.
VARIABLES towers

vars == <<towers>>

Disk == 1 << 0 .. (D - 1)

RECURSIVE SumF(_, _)
SumF(f, S) == IF S = {} THEN 0
              ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumF(f, S \ {x})

TypeOK ==
  /\ towers \in [1 .. N -> 0 .. (1 << D) - 1]
  /\ SumF(towers, 1 .. N) = (1 << D) - 1

Init ==
  /\ towers = [i \in 1 .. N |-> IF i = 1 THEN (1 << D) - 1 ELSE 0]

Move(d, from, to) ==
  /\ from # to
  /\ towers[from] >= d
  /\ (towers[from] \div d) % 2 = 1
  /\ \/ \A k \in 1 .. (D - 1) : ((d >> k) # 0) => ((towers[from] >> k) % 2 = 0)
     \/ \A k \in 1 .. (D - 1) : ((d >> k) # 0) => ((towers[to] >> k) % 2 = 0)
  /\ towers' = [towers EXCEPT ![from] = @ - d, ![to] = @ + d]

Next ==
  \/ \E d \in Disk, from \in 1 .. N, to \in 1 .. N: Move(d, from, to)

Spec == Init /\ [][Next]_vars

\* The goal (all disks on the last tower) is not an invariant; its negation is.
Inv == towers[N] # (1 << D) - 1

====