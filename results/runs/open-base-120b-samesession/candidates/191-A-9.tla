---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

(*-----------------------------------------------------------------
  Derived definitions
-----------------------------------------------------------------*)
Disk(i) == 2 ^ i
Disks   == { Disk(i) : i \in 0..D-1 }

MaxVal  == 2 ^ D - 1

VARIABLE towers

(*-----------------------------------------------------------------
  Type correctness invariant
-----------------------------------------------------------------*)
TypeOK ==
    towers \in [1..N -> Nat] /\ 
    \A i \in 1..N: towers[i] \in 0..MaxVal

(*-----------------------------------------------------------------
  Conservation invariant
-----------------------------------------------------------------*)
Inv == \Sum_{i \in 1..N} towers[i] = MaxVal

(*-----------------------------------------------------------------
  Initial state: all disks on the first tower
-----------------------------------------------------------------*)
Init ==
    /\ towers[1] = MaxVal
    /\ \A i \in 2..N: towers[i] = 0

(*-----------------------------------------------------------------
  Helper: test whether disk d (a power of two) is present on tower t
-----------------------------------------------------------------*)
DiskOn(t, d) == ((t \div d) % 2) = 1

(*-----------------------------------------------------------------
  Move action
-----------------------------------------------------------------*)
Move ==
    \E i \in 0..D-1:
        LET d == Disk(i) IN
            \E s, t \in 1..N:
                /\ s # t
                /\ DiskOn(towers[s], d)          \* d is on source
                /\ towers[s] % d = 0            \* no smaller disk on source
                /\ towers[t] % d = 0            \* destination has no smaller disk
                /\ towers' = [towers EXCEPT 
                                ![s] = towers[s] - d,
                                ![t] = towers[t] + d]

Next == Move

Spec == Init /\ [][Next]_towers

====