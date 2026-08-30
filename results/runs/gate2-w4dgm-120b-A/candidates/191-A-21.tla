---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES towers

vars == <<towers>>

SumOf(f, n) == IF n = 0 THEN 0 ELSE f[n] + SumOf(f, n - 1)

InitAll == (2 ^ D) - 1

Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN InitAll ELSE 0]
  /\ UNCHANGED << >>

Move(disk, src, dst) ==
  /\ src # dst
  /\ towers[src] >= disk
  /\ towers[src] % (2 * disk) >= disk
  /\ towers[dst] % (2 * disk) = 0
  /\ towers' = [towers EXCEPT ![src] = @ - disk, ![dst] = @ + disk]

Next ==
  \E disk \in {2 ^ k : k \in 0..(D - 1)}
  \E src \in 1..N, dst \in 1..N : Move(disk, src, dst)

Spec == Init /\ [][Next]_vars

TypeOK == \A i \in 1..N : towers[i] \in 0..((2 ^ D) - 1)

Inv == SumOf(towers, N) = InitAll
====