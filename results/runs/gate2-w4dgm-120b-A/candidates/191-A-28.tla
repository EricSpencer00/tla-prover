---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

Ats == 1 << 1

\* Tower state is a bitmask: the k-th bit set means the disk of size 2^k
\* rests on that tower. Conservation is the exact bit-sum = 2^D-1.
VARIABLES pegs

vars == <<pegs>>

Disk(k) == 1 << k

RECURSIVE SumOver(_)
SumOver(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN pegs[x] + SumOver(S \ {x})

OnPeg(d) == \E k \in 1..N : pegs[k] >= d

TypeOK ==
  /\ pegs \in [1..N -> 0..(1 << D) - 1]
  /\ SumOver(1..N) = (1 << D) - 1

Init ==
  /\ pegs = [k \in 1..N |-> IF k = 1 THEN (1 << D) - 1 ELSE 0]

Move(d, src, dst) ==
  /\ src # dst
  /\ pegs[src] >= d
  /\ (pegs[src] % (d << 1)) = d
  /\ (pegs[dst] % (d << 1)) = 0
  /\ pegs' = [pegs EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \E d \in {Disk(k) : k \in 0..(D - 1)} :
    \E src \in 1..N : \E dst \in 1..N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

Inv == TypeOK
====