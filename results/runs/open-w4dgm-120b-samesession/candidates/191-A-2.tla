---- MODULE Hanoi ----
EXTENDS Naturals

(* The Tower of Hanoi puzzle, modeled with a bitwise representation of the    *)
(* disk positions.  Each tower's value is the sum of the powers of two        *)
(* identifying the disks present on it; conservation is the sum of those     *)
(* values staying equal to 2^D - 1.                                          *)

CONSTANTS D, N

Total == 2 ^ D - 1

Towers == 1 .. N
Disks == { 2 ^ k : k \in 0 .. (D - 1) }

VARIABLES tower

vars == << tower >>

Sum == tower[1] + tower[2] + tower[3]

TypeOK == /\ tower \in [Towers -> 0 .. Total]
          /\ Total \in Nat

Init == /\ tower = [k \in Towers |-> IF k = 1 THEN Total ELSE 0]

\* A move is valid iff the piece is present on the source, is the smallest
\* piece on the source, and no smaller piece sits on the destination.
Move(p, s, d) == /\ p \in Disks
                 /\ s \in Towers
                 /\ d \in Towers
                 /\ s # d
                 /\ (tower[s] % (p * 2)) >= p
                 /\ (tower[d] % (p * 2)) = 0
                 /\ tower' = [tower EXCEPT ![s] = @ - p, ![d] = @ + p]

Next == \E p \in Disks, s \in Towers, d \in Towers : Move(p, s, d)

Spec == Init /\ [][Next]_vars

Inv == Sum = Total

\* No explicit liveness property: the model checks that the negation of the
\* goal is not invariant, so a counterexample trace is the solution.
====