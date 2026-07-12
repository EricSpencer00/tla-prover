---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

\*-----------------------------------------------------------------
\* Type definitions
\*-----------------------------------------------------------------
Towers == 1..N
Disks == 0..(D-1)          \* disk indices, bit position k represents size 2^k
AllTowers == 1..N

\*-----------------------------------------------------------------
\* Helper functions
\*-----------------------------------------------------------------
\* Bitwise AND using arithmetic: (x /\ y) = Nat2Set(x) /\ Nat2Set(y)
UNARY(x) == ~x

\* Set of disk indices present in a tower value
DiskSet(tower) ==
    { k \in Disks : (tower /\ (1 << k)) = (1 << k) }

\* Smallest disk index present on a tower (0 if empty)
SmallestDisk(tower) ==
    IF tower = 0 THEN 0
    ELSE CHOOSE k \in Disks : (tower /\ (1 << k)) = (1 << k)

\* Tower heights (number of disks)
TowerHeight(tower) == Cardinality(DiskSet(tower))

\*-----------------------------------------------------------------
\* State variables
\*-----------------------------------------------------------------
VARIABLES TowersVals

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init == 
    /\ TowersVals = [t \in Towers |-> 0]
    /\ TowersVals[1] = (1 << D) - 1
    /\ \A t \in Towers \ {1} : TowersVals[t] = 0

\*-----------------------------------------------------------------
\* Move action
\*-----------------------------------------------------------------
Move ==
    \E src \in Towers, dst \in Towers \ {src} :
        /\ src \in Towers /\ dst \in Towers
        /\ TowersVals[src] # 0
        /\ disk = SmallestDisk(TowersVals[src])
        /\ disk > 0
        /\ \A k \in Disks : k < disk => (TowersVals[dst] /\ (1 << k)) = 0
        /\ TowersVals' = [t \in Towers |
                            IF t = src THEN TowersVals[src] - (1 << disk)
                            ELSE IF t = dst THEN TowersVals[dst] + (1 << disk)
                            ELSE TowersVals[t]]
        /\ UNCHANGED << >>

\*-----------------------------------------------------------------
\* Next-state relation
\*-----------------------------------------------------------------
Next == Move

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
Spec == Init /\ [][Next]_<<TowersVals>>

\*-----------------------------------------------------------------
\* Safety invariants
\*-----------------------------------------------------------------
TypeOK == 
    /\ TowersVals \in [Towers -> Nat]
    /\ \A t \in Towers : TowersVals[t] < (1 << D)

Inv == 
    /\ \A t \in Towers : TowersVals[t] = 0 \/ TowersVals[t] < (1 << D)
    /\ TowersVals[1] + TowersVals[2] + ... + TowersVals[N] = (1 << D) - 1

\*-----------------------------------------------------------------
\* END
\*-----------------------------------------------------------------
====