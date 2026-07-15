---- MODULE Hanoi ----
EXTENDS Naturals, TLC

CONSTANT D, N

(*\* Derived constants *)
DiskValues == { 2 ^ i : i \in 0..(D-1) }

(*\* State variable: a function mapping each tower (0..N-1) to the sum of disk values on that tower *)
VARIABLE towers

(*\* Helper: the set of tower indices *)
Towers == 0..(N-1)

(*\* Initial state: all disks on the first tower, all others empty *)
Init ==
    /\ towers = [i \in Towers |-> IF i = 0 THEN 2 ^ D - 1 ELSE 0]
    /\ /\ \A i \in Towers: towers[i] \in Nat
       /\ Sum(towers) = 2 ^ D - 1

(*\* Bitwise AND expressed arithmetically: the result is non‑zero iff the two numbers share a common set bit *)
BitAnd(a, b) ==
    IF a = 0 \/ b = 0 THEN 0
    ELSE
        LET lo == a % 2
            loB == b % 2
            restA == a \div 2
            restB == b \div 2
        IN IF lo = 1 /\ loB = 1 THEN 1 + 2 * BitAnd(restA, restB)
           ELSE 2 * BitAnd(restA, restB)

(*\* The smallest disk on a tower is the least‑significant set bit of its value *)
SmallestDisk(t) ==
    IF t = 0 THEN 0
    ELSE
        LET lo == t % 2
        IN IF lo = 1 THEN 1 ELSE 2 * SmallestDisk(t \div 2)

(*\* A move selects a disk, a source tower, and a destination tower, and updates the tower values *)
Move ==
    \E i \in Towers, j \in Towers, d \in DiskValues :
        /\ i # j
        /\ (towers[i] \ge d)               \* disk present on source
        /\ BitAnd(towers[i], d) = d        \* the bit for d is set
        /\ SmallestDisk(towers[i]) = d     \* d is the smallest on source
        /\ (towers[j] = 0 \/ SmallestDisk(towers[j]) > d) \* destination can accept d
        /\ towers' = [towers EXCEPT ![i] = towers[i] - d,
                                   ![j] = towers[j] + d]

Next ==
    \/ Move
    \/ UNCHANGED towers

Spec ==
    Init /\ [][Next]_<<towers>>

(*\* Safety invariant: the sum of all tower values is conserved *)
Inv ==
    Sum(towers) = 2 ^ D - 1

(*\* Type correctness invariant *)
TypeOK ==
    /\ \A i \in Towers: towers[i] \in Nat
    /\ \A i \in Towers: towers[i] < 2 ^ D

=============================================================================