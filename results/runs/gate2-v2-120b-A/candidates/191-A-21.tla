---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants (to be supplied by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT D \* number of disks, must be >= 1
CONSTANT N \* number of towers, must be >= 2

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
DiskValues == { 2 ^ i : i \in 0..(D - 1) }

\* All possible tower values are natural numbers below 2^D
TowerVals == 0 .. (2 ^ D - 1)

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES towers

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The total sum of all tower values (used in the safety invariant)
TotalSum == 2 ^ D - 1

\* The value representing a disk is a power of two
Disk(d) == d

\* Predicate: d is present on tower t (i.e., the bit for d is set)
DiskOnTower(d, t) == (t \% (2 * d)) >= d

\* Predicate: d is the smallest disk on tower t
SmallestOnTower(d, t) == DiskOnTower(d, t) /\ 
                         \A e \in DiskValues : e < d => ~DiskOnTower(e, t)

\* Predicate: the destination tower t does not contain any disk smaller than d
DestinationAccepts(d, t) == \A e \in DiskValues : e < d => ~DiskOnTower(e, t)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN TotalSum ELSE 0]
    /\ \A i \in 1..N: towers[i] \in TowerVals

\* ----------------------------------------------------------------------
\* Move action (single nondeterministic move)
\* ----------------------------------------------------------------------
Move ==
    \E d \in DiskValues :
      \E src \in 1..N :
        \E dst \in 1..N :
          /\ src # dst
          /\ SmallestOnTower(d, towers[src])
          /\ DestinationAccepts(d, towers[dst])
          /\ towers' = [t \in 1..N |-> 
                         IF t = src THEN towers[t] - d
                         ELSE IF t = dst THEN towers[t] + d
                         ELSE towers[t]]

\* ----------------------------------------------------------------------
\* Stuttering step to keep the model from deadlocking when the goal is reached
\* ----------------------------------------------------------------------
Stutter == UNCHANGED towers

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == Move \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<towers>>

\* ----------------------------------------------------------------------
\* Safety Invariant: type correctness (tower values within range)
\* ----------------------------------------------------------------------
TypeOK == \A i \in 1..N : towers[i] \in TowerVals

\* ----------------------------------------------------------------------
\* Safety Invariant: conservation of total sum of disk values
\* ----------------------------------------------------------------------
Inv == \A i \in 1..N : towers[i] \in TowerVals /\ 
       ( \* optional explicit sum check \*)
       ( \E s \in Nat : s = TotalSum /\ s = \Sum_{i \in 1..N} towers[i] )

\* ----------------------------------------------------------------------
\* The specification to be checked (named as required by the .cfg)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<towers>>

====