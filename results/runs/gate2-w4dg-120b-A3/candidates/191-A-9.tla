---- MODULE Hanoi ----
\* Tower of Hanoi puzzle, where each tower's state is a bitwise sum of disk values.
\* Disks are powers of two, and a tower's value has bit k set iff the disk of
\* size 2^k sits on it. Conservation is checked as a sum over the tower values.
EXTENDS Naturals

CONSTANTS D, N

ASSUME D \in Nat /\ N \in Nat /\ D > 0 /\ N > 1

Disks == { 2 ^ k : k \in 0 .. (D - 1) }

\* Bitwise tests on the natural-number encoding.
HasDisk(v, d) == (v \in Nat /\ d \in Nat /\ (v \cap d) = d)
NoSmaller(v, d) == (v \in Nat /\ d \in Nat /\ (v \cap (d - 1)) = 0)

VARIABLES tower

vars == <<tower>>

RECURSIVE SumSet(_)
SumSet(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN x + SumSet(S \ {x})

TypeOK ==
  /\ tower \in [1 .. N -> 0 .. (2 ^ D - 1)]

Init ==
  /\ tower = [t \in 1 .. N |-> IF t = 1 THEN (2 ^ D - 1) ELSE 0]

\* A single legal disk move between two different towers.
Move(d, s, t) ==
  /\ d \in Disks
  /\ s # t
  /\ HasDisk(tower[s], d)
  /\ NoSmaller(tower[s], d)
  /\ NoSmaller(tower[t], d)
  /\ tower' = [tower EXCEPT ![s] = @ - d, ![t] = @ + d]

Next ==
  \/ \E d \in Disks, s \in 1 .. N, t \in 1 .. N : Move(d, s, t)

\* Conservation: the disks are only ever relocated, never created or destroyed.
Inv ==
  /\ SumSet({tower[t] : t \in 1 .. N}) = (2 ^ D - 1)
  /\ TypeOK

Spec == Init /\ [][Next]_vars

====