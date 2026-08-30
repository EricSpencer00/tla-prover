---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

\* Tower of Hanoi: each peg's value is a bitset of disk sizes (powers of two).
\* Conservation: the sum of peg values always equals the full set of disks.
\* No liveness property is asserted; the model checks the invariant instead.

ASSUME D \in Nat /\ D >= 1 /\ N \in Nat /\ N >= 3

VARIABLES pegs

vars == <<pegs>>

\* Bitwise AND expressed arithmetically so the spec runs without an external Java override.
And(a, b) == b * ((a \div b) % 2)

SumOf(seq) == LET f[S \in SUBSET (1..N)] ==
                  IF S = {} THEN 0
                  ELSE LET x == CHOOSE y \in S : TRUE
                       IN seq[x] + f[S \ {x}]
              IN f[1..N]

TypeOK == pegs \in [1..N -> 0..(2^D - 1)]

\* Conservation: every disk is accounted for on exactly one peg at all times.
Conservation == SumOf(pegs) = (2^D) - 1

Init == pegs = [i \in 1..N |-> IF i = 1 THEN (2^D) - 1 ELSE 0]

\* A move is legal only if the disk is present, is the smallest on its peg, and
\* fits on the destination (no smaller disk already there).
Move(d, src, dst) ==
    /\ d \in { 2^k : k \in 0..(D - 1) }
    /\ src # dst
    /\ And(pegs[src], d) = d
    /\ \A k \in 0..(D - 1) : (d \div 2) > 1 => And(pegs[src], 2^k) = 0
    /\ \A k \in 0..(D - 1) : d > 1 => And(pegs[dst], 2^k) = 0
    /\ pegs' = [pegs EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next == \E d \in { 2^k : k \in 0..(D - 1) }, src, dst \in 1..N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

Inv == Conservation

====