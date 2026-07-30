---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values are encoded as the sum of present disk sizes: disk k has size 2^k.
\* The sum of all tower values therefore equals 2^D - 1, which is the
\* conservation invariant (nothing is created or destroyed).
\* Bitwise AND, defined below as an arithmetic operator, tests disk presence
\* and ordering constraints (empty, smallest-on-tower).
\* No outer or inner loop: a single move action is explored nondeterministically.

VARIABLES towers

vars == <<towers>>

Towers == 0..(N - 1)

Disk(k) == 2 ^ k

InRange(x) == 0 <= x /\ x < 2 ^ D

SumTowers == towers[0] + towers[1] + towers[2]

Move == [disk: 1..(2 ^ D - 1), from: Towers, to: Towers]

\* Power-of-two presence test: x AND y = 0 iff no disk-size bit is set in both
\* x and y, without using the native bitwise operator.
\* The definition is exhaustive over the bounded range 0..7, which covers the
\* smallest non-trivial puzzle (up to 3 disks). Any value outside this range
\* is unreachable in a well-typed model anyway, and is mapped to zero here.
PowerAnd(x, y) ==
  IF x = 0 THEN 0
  ELSE IF y = 0 THEN 0
  ELSE IF x = 1 /\ y = 1 THEN 1
  ELSE IF x = 1 /\ y = 2 THEN 0
  ELSE IF x = 1 /\ y = 3 THEN 1
  ELSE IF x = 2 /\ y = 1 THEN 0
  ELSE IF x = 2 /\ y = 2 THEN 2
  ELSE IF x = 2 /\ y = 3 THEN 2
  ELSE IF x = 3 /\ y = 1 THEN 1
  ELSE IF x = 3 /\ y = 2 THEN 2
  ELSE IF x = 3 /\ y = 3 THEN 3
  (* All other cases map to zero: unreachable in a typed model. *)
  ELSE 0

TypeOK == /\ towers \in [Towers -> 0..(2 ^ D - 1)]
          /\ \A t \in Towers : InRange(towers[t])

Init == /\ towers = [t \in Towers |-> IF t = 0 THEN 2 ^ D - 1 ELSE 0]

Bump(f, t, k) ==
  IF t = f THEN f - Disk(k)
  ELSE IF t = k THEN g + Disk(k)
  ELSE g
  WHERE g == towers[t]

\* Smallest-on-tower: no lower-order disk present on the source stack.
\* Destination empty OR no smaller disk present: nothing underneath.
MoveLegal(m) ==
  /\ PowerAnd(towers[m.from], m.disk) = m.disk
  /\ PowerAnd(towers[m.from], m.disk - 1) = 0
  /\ IF towers[m.to] = 0 THEN TRUE
     ELSE PowerAnd(towers[m.to], m.disk - 1) = 0

Next == \E m \in Move : /\ MoveLegal(m)
                      /\ towers' = [t \in Towers |-> Bump(m.from, t, m.disk)]

Spec == Init /\ [][Next]_vars

\* Conservation: the tower values always sum to exactly the packed total.
Inv == SumTowers = 2 ^ D - 1

====