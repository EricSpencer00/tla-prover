---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower state is encoded as the sum of the power-of-two values of the disks
\* present on each tower; a tower's binary representation is thus its disk set.
\* We constrain the tower values with a custom bitwise AND operator.
\* TLC resolves BitwiseAnd either arithmetically or via a Java override.
\* The spec itself never talks about the Java side.

ASSUME /\ D \in Nat /\ D >= 1
       /\ N \in Nat /\ N >= 2

Disks == {2 ^ k : k \in 0 .. (D - 1)}
None == "none"

VARIABLES towers

vars == << towers >>

RECURSIVE SumOf(_)
SumOf(f) ==
  IF f = << >> THEN 0
  ELSE LET x == CHOOSE e \in DOMAIN f : TRUE
       IN f[x] + SumOf([k \in DOMAIN f \ {x} |-> f[k]])

TypeOK ==
  /\ towers \in [1 .. N -> 0 .. (2 ^ D) - 1]
  /\ SumOf(towers) = (2 ^ D) - 1

Init ==
  /\ towers = [t \in 1 .. N |-> IF t = 1 THEN (2 ^ D) - 1 ELSE 0]

\* A move is valid only if the disk being moved is the smallest one present on
\* the source tower and the destination tower holds no strictly smaller disk.
Move(d, src, dst) ==
  /\ src # dst
  /\ d \in Disks
  /\ BitwiseAnd(towers[src], d) = d
  /\ \A k \in Disks : (k < d /\ BitwiseAnd(towers[src], k) # 0) => FALSE
  /\ \A k \in Disks : (k < d /\ BitwiseAnd(towers[dst], k) # 0) => FALSE
  /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \/ \E d \in Disks, src \in 1 .. N, dst \in 1 .. N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: the disks are never duplicated or lost -- the tower values
\* always sum to exactly the full set of disks.
Inv == TypeOK
====