---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

ASSUME D \in Nat /\ D >= 1 /\ N \in Nat /\ N >= 2

\* A tower is a natural number whose binary bits 0..(D-1) encode which disks
\* are on that peg; tower i's value is the sum of the (power-of-two) disks it
\* holds.  Because every disk is a distinct power of two, the sum of all
\* tower values is conserved: no disk is ever created or destroyed.

RECURSIVE SumTower(_)
SumTower(k) == IF k = 0 THEN 0 ELSE SumTower(k - 1) + t[k - 1]

Disks == { 2 ^ k : k \in 0..(D - 1) }

\* Bitwise AND: the k-th bit of n is 1 iff (n \div 2^k) % 2 = 1.
Bit(k, n) == ((n \div (2 ^ k)) % 2) = 1

SmallestOnTower(i) == CHOOSE k \in 0..(D - 1) : \E m \in 0..(D - 1) : Bit(m, t[i]) => k <= m

\* The smallest disk on a tower is the lowest-order set bit of its value.
\* The destination must be empty or have no disk smaller than the one moved.
MoveLegal(d, src, dst) ==
    \/ (t[dst] = 0)
    \/ (SmallestOnTower(dst) <= SmallestOnTower(src))

TypeOK ==
    /\ t \in [0..(N - 1) -> 0..(2 ^ D - 1)]
    /\ SumTower(N) = 2 ^ D - 1

Init ==
    /\ t = [i \in 0..(N - 1) |-> IF i = 0 THEN 2 ^ D - 1 ELSE 0]

Move(d, src, dst) ==
    /\ src # dst
    /\ Bit(d, t[src])
    /\ SmallestOnTower(src) = d
    /\ MoveLegal(d, src, dst)
    /\ t' = [t EXCEPT ![src] = t[src] - d, ![dst] = t[dst] + d]

Next == \E d \in Disks, src \in 0..(N - 1), dst \in 0..(N - 1) : Move(d, src, dst)

Spec == Init /\ [][Next]_t

Inv == TypeOK

====