---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, TLC

CONSTANT D, N
VARIABLE towers

(*--- definitions of disks ---*)
Disks == { 2 ^ i : i \in 0..(D-1) }

AllDisks == 2 ^ D - 1

(*--- bitwise helpers (using arithmetic) ---*)
IsPresent(t, d) == (t % (2 * d) >= d)

SmallestOn(t, d) ==
  /\ IsPresent(t, d)
  /\ \A d2 \in Disks : d2 < d => ~IsPresent(t, d2)

CanPlace(t, d) ==
  \A d2 \in Disks : d2 < d => ~IsPresent(t, d2)

(*--- initial state ---*)
Init ==
  towers = [i \in 1..N |-> IF i = 1 THEN AllDisks ELSE 0]

(*--- move action ---*)
Next ==
  \/ \E src, dst \in 1..N :
        src # dst /\
        \E d \in Disks :
          /\ IsPresent(towers[src], d)
          /\ SmallestOn(towers[src], d)
          /\ CanPlace(towers[dst], d)
          /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                                    ![dst] = towers[dst] + d]

(*--- specification ---*)
Spec == Init /\ [][Next]_towers

(*--- invariants ---*)
TypeOK ==
  /\ towers \in [1..N -> Nat]
  /\ \A i \in 1..N : towers[i] < 2 ^ D

Inv ==
  /\ \Sum i \in 1..N : towers[i] = AllDisks

====