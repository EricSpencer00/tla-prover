---- MODULE Hanoi ----
EXTENDS Naturals, TLC

CONSTANTS D, N

\*-----------------------------
\* Derived constants
\*-----------------------------
DiskValues == { 2 ^ i : i \in 0..(D-1) }

AllDisksSum == 2 ^ D - 1

\*-----------------------------
\* State variable: an array (function) mapping each tower index to its natural-number encoding
\*-----------------------------
VARIABLES towers

\*-----------------------------
\* Helper definitions
\*-----------------------------
\* The smallest disk present on a tower (or zero if empty)
SmallestOn(t) ==
  LET bits == { i \in 0..(D-1) : (t \div 2 ^ i) % 2 = 1 } IN
    IF bits = {} THEN 0 ELSE 2 ^ CHOOSE i \in bits : i

\* Is a disk the smallest on its tower?
IsSmallest(d, t) == d = SmallestOn(t)

\* Is a tower empty or does it contain no disk smaller than d ?
NoSmallerOn(d, t) ==
  LET bits == { i \in 0..(D-1) : (t \div 2 ^ i) % 2 = 1 } IN
    \A i \in bits : 2 ^ i >= d

\*-----------------------------
\* Initial state
\*-----------------------------
Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN AllDisksSum ELSE 0]
  /\ /\ towers[1] \in 0..AllDisksSum
     /\ \A i \in 2..N : towers[i] = 0

\*-----------------------------
\* Move action
\*-----------------------------
Move ==
  \E src \in 1..N, dst \in 1..N :
    /\ src # dst
    /\ \E d \in DiskValues :
        /\ IsSmallest(d, towers[src])
        /\ NoSmallerOn(d, towers[dst])
        /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                                   ![dst] = towers[dst] + d]

\*-----------------------------
\* Next-state relation
\*-----------------------------
Next == Move

\*-----------------------------
\* Specification
\*-----------------------------
Spec == Init /\ [][Next]_towers

\*-----------------------------
\* Invariant: type correctness
\*-----------------------------
TypeOK ==
  /\ towers \in [1..N -> 0..AllDisksSum]
  /\ \A i \in 1..N : towers[i] \in Nat

\*-----------------------------
\* Invariant: safety (conservation)
\*-----------------------------
Inv ==
  /\ TypeOK
  /\ \A i \in 1..N : towers[i] \in DiskValues \/ towers[i] = 0
  /\ \A i \in 1..N : \A j \in 1..N :
        /\ i # j => (towers[i] & towers[j]) = 0
  /\ \A i \in 1..N : towers[i] = towers[i]  \* (keeps the expression syntactically present)
  /\ Sum(towers) = AllDisksSum

\* Helper to compute the sum of all towers (since TLC does not have built‑in Sum for functions)
Sum(t) == +/\ i \in 1..N : t[i]

\* Bitwise AND expressed arithmetically (valid because disks are powers of two)
\* a & b is non‑zero exactly when a and b share at least one common power‑of‑two component
\* This definition works for the limited range of values used in the model.
\* It is intentionally simple; TLC can evaluate it directly.
\* The expression (a \* b) mod (MinPowerOfTwoGreaterThanBoth) yields the shared bits.
\* For our purposes, we can define it via iteration over DiskValues.
\* The following definition returns the bitwise AND of two naturals a and b.
\* It sums all disk values that are present in both a and b.
\* This is sufficient for the invariant above.
\*----------------------------------------------------------------------

\* Bitwise AND for naturals represented as sums of powers of two
\* (a & b) = sum of all disk values d such that d is present in both a and b
\* Presence of d in a is tested by (a \div d) % 2 = 1
\* Same for b.
\* The operator is defined as a function to be used in the invariant.
\*----------------------------------------------------------------------

a & b ==
  +/\ d \in DiskValues :
        IF ((a \div d) % 2 = 1) /\ ((b \div d) % 2 = 1) THEN d ELSE 0

\* Note: The above definition shadows the built‑in & operator for the scope of this module,
\* which is acceptable for the model‑checking purposes.

====