---- MODULE Hanoi ----
EXTENDS Naturals, TLC

\* -----------------------------------------------------------------
\* Constants (to be given values in the .cfg file)
\* -----------------------------------------------------------------
CONSTANT D      \* number of disks
CONSTANT N      \* number of towers (pegs)

\* -----------------------------------------------------------------
\* Derived constants
\* -----------------------------------------------------------------
DiskSet == 1 .. (2 ^ D - 1)          \* bit masks for all possible disks (powers of two)
Towers  == 1 .. N

\* -----------------------------------------------------------------
\* State variables
\* -----------------------------------------------------------------
VARIABLES towers

\* -----------------------------------------------------------------
\* Helper definitions
\* -----------------------------------------------------------------
\* The value representing all disks present (initial sum)
AllDisks == 2 ^ D - 1

\* A disk is a power of two within the range 1..AllDisks
Disk(d) == d \in DiskSet /\ d = 1 << LogBase2(d)

\* LogBase2 returns the exponent k such that 2^k = d (for powers of two)
LogBase2(d) == 
    IF d = 1 THEN 0
    ELSE 1 + LogBase2(d \div 2)

\* The smallest disk present on a tower (or 0 if the tower is empty)
SmallestOn(t) ==
    IF towers[t] = 0 THEN 0
    ELSE
        CHOOSE d \in DiskSet :
            /\ (towers[t] /\ d) = d          \* d is present on tower t
            /\ \A d2 \in DiskSet :
                (d2 < d) => ((towers[t] /\ d2) = 0)   \* no smaller disk present

\* The set of disks that are present on a given tower
DisksOn(t) == { d \in DiskSet : (towers[t] /\ d) = d }

\* -----------------------------------------------------------------
\* Initialization
\* -----------------------------------------------------------------
Init ==
    /\ towers = [i \in Towers |-> IF i = 1 THEN AllDisks ELSE 0]

\* -----------------------------------------------------------------
\* Move action
\* -----------------------------------------------------------------
Move ==
    \E d \in DiskSet :
      \E src \in Towers :
        \E dst \in Towers :
          /\ src # dst
          /\ (towers[src] /\ d) = d                  \* disk d is on source
          /\ SmallestOn(src) = d                     \* d is the smallest on src
          /\ (towers[dst] = 0 \/ ((towers[dst] /\ d) = 0 /\ SmallestOn(dst) # 0))
               /\ \A d2 \in DiskSet :
                     (d2 < d) => ((towers[dst] /\ d2) = 0)   \* no smaller on dst
          /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                                       ![dst] = towers[dst] + d]

Next == Move

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_<<towers>>

\* -----------------------------------------------------------------
\* Safety invariants
\* -----------------------------------------------------------------
TypeOK ==
    /\ towers \in [Towers -> Nat]
    /\ \A t \in Towers : towers[t] \in 0..AllDisks
    /\ \A t \in Towers : towers[t] = 0 \/ 
          (\A k \in 0..(D-1) : ((towers[t] >> k) # 0) => ((towers[t] >> k) = 1 << k))
         \* each set bit corresponds to a single disk (power of two)

Inv ==
    /\ \A t \in Towers : towers[t] >= 0
    /\ \A t \in Towers : towers[t] <= AllDisks
    /\ \A t \in Towers : \A d \in DiskSet :
          ( (towers[t] /\ d) = d ) => d \in DiskSet
    /\ \A t \in Towers : \A d1, d2 \in DiskSet :
          ( (towers[t] /\ d1) = d1 /\ (towers[t] /\ d2) = d2 ) =>
          (d1 # d2 => (d1 # d2))
    /\ \Sum_{t \in Towers} towers[t] = AllDisks

\* -----------------------------------------------------------------
\* Theorem (optional, not required by .cfg but useful for TLC)
\* -----------------------------------------------------------------
THEOREM Spec => []Inv

====