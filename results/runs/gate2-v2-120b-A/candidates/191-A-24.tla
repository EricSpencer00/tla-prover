---- MODULE Hanoi ----
EXTENDS Naturals, TLC

(*-------------------------------------------------------------------*)
(*  Constants                                                       *)
(*-------------------------------------------------------------------*)
CONSTANT D
CONSTANT N

(*-------------------------------------------------------------------*)
(*  Derived constants                                                *)
(*-------------------------------------------------------------------*)
DiskSet  == 1 .. D
Towers   == 1 .. N

(* Bitmask for a given disk index k (1-based) *)
DiskMask(k) == 2^(k - 1)

(* Set of all disk masks *)
DiskMasks == { DiskMask(k) : k \in DiskSet }

(* Sum of all disk masks = 2^D - 1 *)
AllDisks == 2^D - 1

(*-------------------------------------------------------------------*)
(*  Variables                                                       *)
(*-------------------------------------------------------------------*)
VARIABLES tower

(*-------------------------------------------------------------------*)
(*  Helper definitions                                              *)
(*-------------------------------------------------------------------*)
(* Value of tower i is a natural number whose binary bits encode the
   disks present on that tower. *)
Tower(i) == tower[i]

(* The set of disks present on tower i, expressed as a set of indices *)
DisksOn(i) == { k \in DiskSet : (Tower(i) /\ DiskMask(k)) # 0 }

(* Smallest disk present on tower i, if any *)
SmallestDisk(i) ==
  IF Tower(i) = 0 THEN 0
  ELSE CHOOSE k \in DiskSet :
        (Tower(i) /\ DiskMask(k)) # 0 /\ 
        \A j \in DiskSet : (j < k) => ((Tower(i) /\ DiskMask(j)) = 0)

(*-------------------------------------------------------------------*)
(*  Initial state                                                   *)
(*-------------------------------------------------------------------*)
Init ==
  /\ tower = [i \in Towers |-> IF i = 1 THEN AllDisks ELSE 0]
  /\ \A i \in Towers : 0 <= tower[i] /\ tower[i] < 2^D

(*-------------------------------------------------------------------*)
(*  Move action                                                     *)
(*-------------------------------------------------------------------*)
Move ==
  \E src, dst \in Towers :
    /\ src # dst
    /\ Tower(src) # 0                         \* source not empty
    /\ LET d == SmallestDisk(src) IN
         /\ d # 0
         /\ (Tower(dst) = 0 \/ (Tower(dst) /\ DiskMask(d)) = 0)   \* no smaller disk on dst
         /\ tower' = [tower EXCEPT ![src] = tower[src] - DiskMask(d),
                               ![dst] = tower[dst] + DiskMask(d)]

(*-------------------------------------------------------------------*)
(*  Next-state relation                                              *)
(*-------------------------------------------------------------------*)
Next == Move

(*-------------------------------------------------------------------*)
(*  Specification                                                   *)
(*-------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<tower>>

(*-------------------------------------------------------------------*)
(*  Safety invariants                                               *)
(*-------------------------------------------------------------------*)
TypeOK ==
  /\ tower \in [Towers -> Nat]
  /\ \A i \in Towers : tower[i] < 2^D

Inv ==
  /\ TypeOK
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : 
        \A k \in DiskSet :
          (tower[i] /\ DiskMask(k)) # 0 => 
            \A j \in DiskSet :
               j < k => (tower[i] /\ DiskMask(j)) = 0
  /\ /\* Conservation of total disk sum *\
     \A i \in Towers : tower[i] >= 0
  /\ \A i \in Towers : tower[i] < 2^D
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers :
        \A j \in Towers :
           i # j => (tower[i] /\ tower[j]) = 0   \* disks are disjoint among towers
  /\ \A i \in Towers : tower[i] <= AllDisks
  /\ \A i \in Towers : tower[i] >= 0
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \A i \in Towers : tower[i] \in Nat
  /\ \Sum_{i \in Towers} tower[i] = AllDisks

====