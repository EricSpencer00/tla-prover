---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS D, N

VARIABLES towers

(*---------------------------------------------------------------------*)
(* Helper definitions *)
(*---------------------------------------------------------------------*)

Disk(i) == 2 ^ i

DiskSet == { Disk(i) : i \in 0..(D-1) }

(* Is the disk d present on tower value t? *)
IsOn(t, d) == ((t \div d) % 2) = 1

(* Are there no disks smaller than d on tower value t? *)
NoSmaller(t, d) == t % d = 0

(* Disk d is the smallest disk on tower value t *)
SmallestOn(t, d) == IsOn(t, d) /\ NoSmaller(t, d)

(*---------------------------------------------------------------------*)
(* Initialization *)
(*---------------------------------------------------------------------*)

Init ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N: 
          IF i = 1 
          THEN towers[i] = (2 ^ D) - 1 
          ELSE towers[i] = 0

(*---------------------------------------------------------------------*)
(* Next-state relation *)
(*---------------------------------------------------------------------*)

Move ==
    \E s, dst \in 1..N:
        /\ s # dst
        /\ \E d \in DiskSet:
               /\ SmallestOn(towers[s], d)
               /\ NoSmaller(towers[dst], d)
               /\ towers' = [towers EXCEPT ![s] = towers[s] - d,
                                      ![dst] = towers[dst] + d]

Next == Move \/ UNCHANGED towers

(*---------------------------------------------------------------------*)
(* Specification *)
(*---------------------------------------------------------------------*)

Spec == Init /\ [][Next]_towers

(*---------------------------------------------------------------------*)
(* Invariants *)
(*---------------------------------------------------------------------*)

TypeOK ==
    /\ \A i \in 1..N: towers[i] \in Nat
    /\ \A i \in 1..N: towers[i] < (2 ^ D)

Inv ==
    \* Conservation of total disk value
    \E total == \Sum i \in 1..N: towers[i] : total = (2 ^ D) - 1

(*---------------------------------------------------------------------*)
(* THEOREMS (optional, for TLC) *)
(*---------------------------------------------------------------------*)

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv

====