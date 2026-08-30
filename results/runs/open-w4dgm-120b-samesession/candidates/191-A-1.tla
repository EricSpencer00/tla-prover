---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower states are encoded as the sum of the values of the disks they hold,
\* where each disk's size is a distinct power of two.  A bitwise AND test
\* isolates the smallest disk on a tower (lower bits zero) -- the legal
\* "top of stack" marker for this puzzle.
VARIABLES towers

vars == <<towers>>

TypeOK == towers \in [1..N -> 0..(2^D - 1)]

\* Disk k has value 2^k (k=0 is the smallest).  The puzzle conserves disk
\* material: the sum of all tower values is always the packed sum of every
\* disk exactly once.
Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]
  /\ UNCHANGED towers

Move(d, s, t) ==
  /\ s \in 1..N /\ t \in 1..N /\ s # t
  /\ d \in 1..2^D-1 /\ d \in {2^k : k \in 0..(D-1)}
  /\ towers[s] >= d
  /\ towers[s] % (2 * d) = d
  /\ towers[t] % (2 * d) = 0
  /\ towers' = [towers EXCEPT ![s] = towers[s] - d, ![t] = towers[t] + d]

Next == \E d \in 1..2^D-1, s \in 1..N, t \in 1..N : Move(d, s, t)

Spec == Init /\ [][Next]_vars

\* Conservation: the fixed sum of all tower values can only hold if no bitwise
\* move ever creates or destroys a disk value.
Inv == (towers[1] + towers[2] + towers[3]) = 2^D - 1

====