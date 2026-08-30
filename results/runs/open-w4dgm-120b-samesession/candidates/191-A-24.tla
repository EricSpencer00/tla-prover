---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

ASSUME D \in Nat /\ D >= 1 /\ N \in Nat /\ N >= 2

RECURSIVE SumOver(_)
SumOver(n) == IF n = 0 THEN 0 ELSE SumOver(n - 1) + Hanoi[n - 1]

VARIABLES towers

vars == << towers >>

Disk(k) == 2 ^ k
SumAll == 2 ^ D - 1

TypeOK ==
  /\ towers \in [0 .. N - 1 -> 0 .. SumAll]
  /\ SumOver(N) = SumAll

Init ==
  /\ towers = [i \in 0 .. N - 1 |-> IF i = 0 THEN SumAll ELSE 0]

\* Move a disk (a power of two) from one tower to another, but only if it is the
\* smallest disk on its source tower and the destination has no smaller disk.
Move(d, i, j) ==
  /\ i # j
  /\ d \in {Disk(k) : k \in 0 .. D - 1}
  /\ (towers[i] & d) = d
  /\ (towers[i] & ((d << 1) - 1)) = 0
  /\ (towers[j] = 0 \/ (towers[j] & (d - 1)) = 0)
  /\ towers' = [towers EXCEPT ![i] = @ - d, ![j] = @ + d]

Next ==
  \E d \in {Disk(k) : k \in 0 .. D - 1} \E i \in 0 .. N - 1 \E j \in 0 .. N - 1 : Move(d, i, j)

Spec == Init /\ [][Next]_vars

\* The puzzle is solved exactly when the last tower holds every disk; the
\* specification checks that not-all-on-last is not the case forever.
Inv == towers[N - 1] # SumAll

====