---- MODULE Hanoi ----
EXTENDS Naturals

(* Tower of Hanoi: tower values encode disk occupancy as a sum of powers of two,
   so the bitwise structure of a tower's value is the whole rule set. *)
CONSTANTS D, N

Disks == { 2 ^ k : k \in 0 .. (D - 1) }

VARIABLES tower

vars == <<tower>>

Range(t) == IF t < 0 THEN 0 ELSE (CHOOSE k \in 0 .. N : t < 2 ^ k) - 1

SumOfTowers == tower[1] + tower[2] + tower[3]

TypeOK ==
  /\ tower \in [1 .. N -> 0 .. (2 ^ D) - 1]
  /\ SumOfTowers = (2 ^ D) - 1

Init ==
  /\ tower = [i \in 1 .. N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

OnTop(t) == LET lo == ((tower[t] - 1) % (2 * tower[t])) \* lowest set bit
            IN IF tower[t] = 0 THEN 0 ELSE lo

Move(d, src, dst) ==
  /\ src # dst
  /\ (tower[src] % (2 * d)) = d
  /\ ((tower[src] - d) % (2 * d)) = 0
  /\ ((tower[dst] % (2 * d)) = 0 \/ tower[dst] = 0)
  /\ tower' = [tower EXCEPT ![src] = tower[src] - d, ![dst] = tower[dst] + d]

Next ==
  \/ \E d \in Disks, src \in 1 .. N, dst \in 1 .. N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

====