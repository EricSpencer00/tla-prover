---- MODULE Hanoi ----
EXTENDS Naturals, TLC

CONSTANTS D, N

VARIABLES towers

(* Maximum value representing all disks present *)
MaxVal == 2^D - 1

(* Set of disk values – each a distinct power of two *)
DiskSet == { 2^k : k \in 0..D-1 }

(* Helper predicates *)

(* Disk d is present on tower i in the current state *)
IsOn(d, i) == (towers[i] % (2 * d)) >= d

(* Disk d is the smallest disk on tower i (no lower‑order bits set) *)
SmallestOn(d, i) == towers[i] % d = 0

(* Destination tower i has no disk smaller than d *)
DestinationOk(d, i) == towers[i] % d = 0

(* Initial state: all disks on the first tower *)
Init == 
    /\ towers = [i \in 1..N |-> IF i = 1 THEN MaxVal ELSE 0]

(* One legal move *)
Next == 
    \E d \in DiskSet:
      \E s \in 1..N:
        \E t \in 1..N:
          /\ s # t
          /\ IsOn(d, s)
          /\ SmallestOn(d, s)
          /\ DestinationOk(d, t)
          /\ towers' = [i \in 1..N |-> 
                         IF i = s THEN towers[i] - d
                         ELSE IF i = t THEN towers[i] + d
                         ELSE towers[i]]

(* Overall specification *)
Spec == Init /\ [] [Next]_<<towers>>

(* Type correctness invariant *)
TypeOK == 
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N: towers[i] \in 0..MaxVal

(* Conservation invariant *)
Inv == (\Sum i \in 1..N: towers[i]) = MaxVal

====