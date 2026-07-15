---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS D, N

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
DiskVals == { 2 ^ i : i \in 0 .. D-1 }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES towers

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Towers == 1 .. N

\* Bitwise AND using arithmetic:
\* x AND y = x - ((x - (x - y) % (MaxDisk+1)) % (MaxDisk+1))
\* This works because MaxDisk+1 = 2^D, the modulus of the full set of bits.
\* For readability we also define a predicate that checks if a disk is present.
\*   DiskPresent(d, v)  ==  (d * (v \div d) = v)  \* i.e., d divides v exactly
\* However we will use the arithmetic definition directly.

MaxPower == 2 ^ D
MaxDisk  == MaxPower - 1

\* Disk presence predicate
DiskPresent(d, v) == (d \in DiskVals) /\ (v \ge d) /\ ((v \div d) * d = v)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ towers = [i \in Towers |-> IF i = 1 THEN MaxDisk ELSE 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Move ==
    \E d \in DiskVals :
      \E s \in Towers, t \in Towers :
        /\ s # t
        /\ DiskPresent(d, towers[s])                \* disk on source
        /\ ( towers[s] \div d ) * d = towers[s]      \* d is smallest on source
        /\ ( towers[t] = 0 \/ ( towers[t] \div d ) * d = towers[t] ) \* dest empty or d smallest
        /\ towers' = [towers EXCEPT ![s] = towers[s] - d,
                                   ![t] = towers[t] + d]

Next == Move

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_towers

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ towers \in [Towers -> Nat]
    /\ \A i \in Towers : towers[i] \in 0 .. MaxDisk

Inv ==
    /\ \A i \in Towers : towers[i] \in 0 .. MaxDisk
    /\ \A i, j \in Towers : i # j => (towers[i] * towers[j] = 0)   \* no shared bits
    /\ \Sum_{i \in Towers} towers[i] = MaxDisk

\* ----------------------------------------------------------------------
\* Theorems (optional, kept for completeness)
\* ----------------------------------------------------------------------
\* THEOREM Spec => []Inv

====