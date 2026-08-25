---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Disk == { 2^k : k \in 0..D-1 }

DiskOn(tower, d) == ((towers[tower] \div d) % 2) = 1

SmallestOn(tower, d) == (towers[tower] % d) = 0

NoSmallerOn(tower, d) == (towers[tower] % d) = 0

(*--------------------------------------------------------------------
  Sum over a set of natural numbers (recursive definition)
--------------------------------------------------------------------*)
Sum(S) == 
    IF S = {} THEN 0 
    ELSE LET x == CHOOSE y \in S: TRUE 
         IN x + Sum(S \ {x})

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ towers[1] = 2^D - 1
    /\ \A i \in 2..N: towers[i] = 0

(*--------------------------------------------------------------------
  Next-state relation (a legal move)
--------------------------------------------------------------------*)
Next ==
    \E s \in 1..N:
      \E dst \in 1..N:
        /\ s # dst
        /\ \E d \in Disk:
            /\ DiskOn(s, d)               \* the disk is on the source tower
            /\ SmallestOn(s, d)           \* it is the smallest disk there
            /\ NoSmallerOn(dst, d)        \* destination has no smaller disk
            /\ towers' = [towers EXCEPT
                            ![s]   = towers[s] - d,
                            ![dst] = towers[dst] + d]

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<towers>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeOK ==
    /\ \A i \in 1..N: towers[i] \in Nat
    /\ \A i \in 1..N: towers[i] < 2^D

Inv ==
    /\ TypeOK
    /\ Sum({towers[i] : i \in 1..N}) = 2^D - 1

====