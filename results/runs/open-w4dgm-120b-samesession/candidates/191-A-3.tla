---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

ASSUME D \in Nat /\ D > 0 / N \in Nat /\ N >= 2

Disks == { 2 ^ k : k \in 0..(D - 1) }
Towers == 1..N
Total == 2 ^ D - 1

VARIABLES value

vars == <<value>>

TypeOK ==
  /\ value \in [Towers -> Nat]
  /\ \A t \in Towers : value[t] >= 0 /\ value[t] < 2 ^ D

Init ==
  /\ value = [t \in Towers |-> IF t = 1 THEN Total ELSE 0]

Move ==
  /\ \E disk \in Disks :
       /\ \E src \in Towers, dst \in Towers :
            /\ src # dst
            /\ disk <= value[src]
            /\ (value[src] % (disk * 2)) >= disk
            /\ (IF value[dst] = 0 THEN TRUE ELSE value[dst] % (disk * 2) = 0)
            /\ value' = [value EXCEPT ![src] = @ - disk, ![dst] = @ + disk]
  /\ UNCHANGED << >>

Spec == Init /\ [][Move]_vars

Conservation == value[1] + value[2] + value[3] = Total

Inv == TypeOK /\ Conservation

====