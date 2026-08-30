---- MODULE Hanoi ----
\* Tower of Hanoi puzzle modeled with a bitwise tower encoding: each tower's
\* value is the sum of its disk sizes, and since all disk sizes are powers of
\* two, the binary bits of a tower uniquely identify which disks sit there.
\* A move removes a disk from its source tower and adds it to its destination
\* tower, but only if that disk is the smallest on the source tower and the
\* destination tower has no smaller disk already on it. Entailment is a
\* global arithmetic fact: the sum of all tower values is always exactly
\* 2^D - 1, the sum of every disk size from 1 to 2^(D-1), so no disk is ever
\* created or destroyed by any move.
EXTENDS Naturals

CONSTANTS D, N

Disks == (2 ^ D) - 1

VARIABLES towers

vars == <<towers>>

TypeOK == towers \in [1..N -> 0..Disks]

Init == towers = [i \in 1..N |-> IF i = 1 THEN Disks ELSE 0]

\* Moves are nondeterministic: the spec explores every legal move, not a
\* particular solution strategy. Bitwise AND (encoded arithmetically) checks
\* that the moving disk is on the source and that nothing below it blocks
\* either the source or the destination.
Move(d, s, t) ==
  /\ s # t
  /\ towers[s] >= d
  /\ towers[s] % (2 * d) = d
  /\ towers[t] % (2 * d) = 0
  /\ towers' = [towers EXCEPT ![s] = @ - d, ![t] = @ + d]

Next == \E d \in 1..Disks, s \in 1..N, t \in 1..N : Move(d, s, t)

Spec == Init /\ [][Next]_vars

\* Conservation: the bitwise accounting of disks across all towers always matches
\* the fixed total Disk sum -- this is the property that would fail if a move
\* accidentally duplicated or dropped a disk.
Conservation ==
  LET f[i \in 1..N] == IF i = 1 THEN towers[i] ELSE towers[i] + f[i - 1] IN f[N] = Disks

TypeOKInv == TypeOK

\* The goal state (all disks stacked on the last tower) is not forced by any
\* invariant; instead the model checks the negation of that goal as an
\* invariant, so a bounded model-checking run that disproves it is exactly a
\* proof that the puzzle can be solved from the starting configuration.
GoalNotReached == towers[N] # Disks

====