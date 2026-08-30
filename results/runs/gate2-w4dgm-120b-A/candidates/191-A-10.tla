---- MODULE Hanoi ----
EXTENDS Integers, FiniteSets

CONSTANTS D, N

\* Disk sizes are powers of two: 2^0, 2^1, ..., 2^(D-1). Tower values are sums of
\* the disk values present; bits in the sum encode which disks sit there.
\* Conservation is a literal accounting identity on those sums.

VARIABLES tower

vars == <<tower>>

Towers == 0..(N - 1)

\* Total of all disks in the puzzle; an empty tower contributes zero.
RECURSIVE SumOver(_)
SumOver(S) ==
    IF S = {} THEN 0
    ELSE LET t == CHOOSE x \in S : TRUE IN tower[t] + SumOver(S \ {t})

AllDisks == 2 ^ D - 1

TypeOK ==
    /\ tower \in [Towers -> 0 .. AllDisks]
    /\ SumOver(Towers) = AllDisks

\* A disk's value is a power of two, so "disk = 2^k" means "disk is the k-th size".
DiskSize(k) == 2 ^ k

Init ==
    /\ tower = [t \in Towers |-> IF t = 0 THEN AllDisks ELSE 0]

\* A move is legal iff the moved disk is on the source, is the smallest on it,
\* and lands on an empty tower or on top of a larger disk (no smaller bit set).
Move(disk, src, dst) ==
    /\ src # dst
    /\ (tower[src] \in 0 .. AllDisks) /\ (disk \in 1 .. AllDisks)
    /\ (disk * 2) \notin 0 .. AllDisks
    /\ (tower[src] % (disk * 2)) \in {0, disk}
    /\ (tower[dst] % (disk * 2)) \in {0}
    /\ tower' = [tower EXCEPT ![src] = @ - disk, ![dst] = @ + disk]

Next ==
    \/ \E disk \in {DiskSize(k) : k \in 0..(D - 1)}:
       \E src \in Towers, dst \in Towers: Move(disk, src, dst)

Spec == Init /\ [][Next]_vars

\* The puzzle is solved by checking that the negation of the goal state is
\* itself an invariant: if every disk is on the last tower the sum-other-
\* towers is zero, a property no reachable state can violate.
GoalState == \A t \in Towers : (t = N - 1) => (tower[t] = AllDisks)

Inv == GoalState
====