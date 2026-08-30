---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

ASSUME D \in Nat /\ D >= 1 /\ N \in Nat /\ N >= 2

VARIABLES tower

vars == <<tower>>

RECURSIVE SumF(_, _)
SumF(f, k) == IF k = 0 THEN 0 ELSE f[k] + SumF(f, k - 1)

\* Each tower's integer value is the binary encoding of its disk stack: bit k
\* (value 2^k) means the disk of that size is present on that tower.
\* Conservation of mass: the total weight across all towers must be invariant.
TotalWeight == 2 ^ D - 1

TypeOK ==
  /\ tower \in [1..N -> 0..TotalWeight]
  /\ SumF(tower, N) = TotalWeight

Init ==
  /\ tower = [i \in 1..N |-> IF i = 1 THEN TotalWeight ELSE 0]

\* A move is legal only if the disk is present on the source, is the smallest
\* disk there, and would not be placed on a smaller disk at the destination.
Move(disk, from, to) ==
  /\ from # to
  /\ tower[from] >= disk
  /\ (tower[from] \div 2) * 2 = tower[from] - disk
  /\ (tower[to] = 0 \/ (tower[to] \div 2) * 2 = tower[to])
  /\ tower' = [tower EXCEPT ![from] = @ - disk, ![to] = @ + disk]

Next ==
  \E disk \in (1 :> (2 ^ (D - 1)) @@ (2 :> (2 ^ (D - 1))) :> (2 ^ (D - 1))), from \in 1..N, to \in 1..N : Move(disk, from, to)

Spec ==
  /\ Init
  /\ [][Next]_vars

\* The puzzle is solved when every disk rests on the last tower, so the
\* negation of the goal state can serve as a simple invariant to falsify.
GoalStateInvariance ==
  \A i \in 1..N : i # N => tower[i] # TotalWeight

====