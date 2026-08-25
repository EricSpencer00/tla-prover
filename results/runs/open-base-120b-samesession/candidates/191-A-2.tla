---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(*--------------------------------------------------------------------*)
(* Helper definitions *)

MaxVal == 2^D - 1

DiskSet == { 2^i : i \in 0..(D-1) }

(*--------------------------------------------------------------------*)
(* Initial state *)

Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN MaxVal ELSE 0]

(*--------------------------------------------------------------------*)
(* Move action *)

Move ==
    \E src, dst \in 1..N :
        /\ src # dst
        /\ \E disk \in DiskSet :
            /\ (towers[src] % (2 * disk)) = disk          \* disk is present and smallest on src
            /\ (towers[dst] % (2 * disk)) = 0             \* no smaller disk on dst
            /\ towers' = [towers EXCEPT
                            ![src] = towers[src] - disk,
                            ![dst] = towers[dst] + disk]

Next == Move

(*--------------------------------------------------------------------*)
(* Specification *)

Spec == Init /\ [][Next]_<<towers>>

(*--------------------------------------------------------------------*)
(* Invariants *)

TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] \in 0..MaxVal

Inv ==
    \Sum i \in 1..N : towers[i] = MaxVal

====