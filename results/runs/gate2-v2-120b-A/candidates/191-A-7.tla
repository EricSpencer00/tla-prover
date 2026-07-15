---- MODULE Hanoi ----
EXTENDS Naturals, Sequences

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT D \* number of disks
CONSTANT N \* number of towers

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
ALLDISKS == 2 ^ D - 1

DISKS == { 2 ^ i : i \in 0..(D - 1) }

Towers == 0..(N - 1)

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLE tower

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
(* Bitwise AND for natural numbers, defined arithmetically. *)
BitAnd(m, n) ==
  LET max == MAX(m, n) + 1 IN
  Sum({ 2 ^ i : i \in 0..(max - 1) : ((m % (2 ^ (i + 1))) >= 2 ^ i) /\ ((n % (2 ^ (i + 1))) >= 2 ^ i) })

(* The smallest disk present on tower t, or 0 if the tower is empty. *)
SmallestDisk(t) ==
  IF tower[t] = 0 THEN 0
  ELSE
    LET bits == { i \in 0..(D - 1) : (tower[t] % (2 ^ (i + 1))) >= 2 ^ i } IN
    2 ^ Min(bits)

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ tower = [t \in Towers |-> IF t = 0 THEN ALLDISKS ELSE 0]
  /\ TypeOK

(*--------------------------------------------------------------------
  Type correctness invariant (used as a helper for the main invariant)
--------------------------------------------------------------------*)
TypeOK ==
  /\ tower \in [Towers -> 0..ALLDISKS]
  /\ \A t \in Towers : tower[t] \in 0..ALLDISKS

(*--------------------------------------------------------------------
  Move action
--------------------------------------------------------------------*)
Move ==
  \E src \in Towers, dst \in Towers, d \in DISKS :
    /\ src # dst
    /\ (tower[src] % (2 * d)) >= d           \* disk d is present on src
    /\ (tower[src] % d) = 0                  \* d is the smallest on src
    /\ (tower[dst] % d) = 0                  \* no smaller disk on dst
    /\ tower' = [tower EXCEPT ![src] = tower[src] - d,
                              ![dst] = tower[dst] + d]
    /\ TypeOK

Next == Move

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<tower>>

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
(* Conservation of total disk weight *)
Inv ==
  /\ \A t \in Towers : tower[t] \in 0..ALLDISKS
  /\ Sum(tower) = ALLDISKS

=============================================================================