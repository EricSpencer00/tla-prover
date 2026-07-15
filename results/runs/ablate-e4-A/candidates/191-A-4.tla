---- MODULE Hanoi ----
EXTENDS Naturals, TLC, BitVector

CONSTANTS D, N

VARIABLES Towers

(* Helper sets *)
TowersSet == 1..N
DiskValues == { 2^k | k \in 0..(D-1) }

(* Initial state *)
Init ==
    Towers = [t \in TowersSet |-> IF t = 1 THEN 2^D - 1 ELSE 0]

(* Valid move predicate *)
ValidMove(src, dest, d) ==
    /\ (Towers[src] \& d) # 0
    /\ (Towers[src] \& (d - 1)) = 0
    /\ (Towers[dest] \& (d - 1)) = 0

(* Next-state action *)
Next ==
    \/ \E src, dest \in TowersSet : src # dest :
          \E d \in DiskValues : ValidMove(src, dest, d)
              /\ Towers' = [t \in TowersSet |
                               IF t = src THEN Towers[t] - d
                               ELSE IF t = dest THEN Towers[t] + d
                               ELSE Towers[t]]

(* Type correctness invariant *)
TypeOK ==
    /\ Towers \in [TowersSet -> Nat]
    /\ \A t \in TowersSet : Towers[t] < 2^D

(* Conservation invariant *)
Inv ==
    /\ TypeOK
    /\ (SUM t \in TowersSet : Towers[t] = 2^D - 1)

(* Specification *)
Spec == Init /\ [][Next]_Towers

====