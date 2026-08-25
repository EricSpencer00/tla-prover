---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS D, N

VARIABLES tower

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
DiskSet == { 2 ^ i : i \in 0..(D - 1) }

AllDisks == 2 ^ D - 1

(*-----------------------------------------------------------------
  Helper predicates
-----------------------------------------------------------------*)
DiskOn(t, d) == ((t \div d) % 2) = 1

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ tower = [i \in 1..N |-> IF i = 1 THEN AllDisks ELSE 0]

(*-----------------------------------------------------------------
  Move action
-----------------------------------------------------------------*)
Move ==
    \E src, dst \in 1..N :
        /\ src # dst
        /\ \E d \in DiskSet :
            /\ DiskOn(tower[src], d)          \* disk d is present on src
            /\ tower[src] % d = 0             \* d is the smallest on src
            /\ tower[dst] % d = 0             \* no smaller disk on dst
            /\ tower' = [tower EXCEPT
                           ![src] = tower[src] - d,
                           ![dst] = tower[dst] + d]

Next ==
    \/ Move
    \/ UNCHANGED tower

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<tower>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK ==
    /\ tower \in [1..N -> Nat]
    /\ \A i \in 1..N : tower[i] < 2 ^ D

Inv ==
    /\ TypeOK
    /\ (\SUM i \in 1..N : tower[i]) = AllDisks

====