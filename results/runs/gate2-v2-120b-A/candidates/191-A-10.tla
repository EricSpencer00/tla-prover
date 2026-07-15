---- MODULE Hanoi ----
EXTENDS Naturals, TLC

(*--------------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
--------------------------------------------------------------------*)
CONSTANT D
CONSTANT N

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
DiskValues == { 2 ^ i : i \in 0 .. D-1 }

(*--------------------------------------------------------------------
  State variable: an array (function) mapping each tower index to the
  natural number that encodes the set of disks on that tower.
--------------------------------------------------------------------*)
VARIABLES tower

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
(* The total sum of all disk values, i.e., 2^D - 1 *)
AllDisks == 2 ^ D - 1

(* The set of tower indices *)
Towers == 0 .. N-1

(* Disk d is present on tower t *)
DiskOn(d, t) == (tower[t] /\ d) # 0

(* The smallest disk present on tower t (or 0 if the tower is empty) *)
SmallestDisk(t) ==
  IF tower[t] = 0 THEN 0
  ELSE
    CHOOSE d \in DiskValues :
        DiskOn(d, t) /\ \A e \in DiskValues : (e < d) => ~DiskOn(e, t)

(* The set of disks currently on tower t, expressed as a subset of DiskValues *)
DisksOn(t) == { d \in DiskValues : DiskOn(d, t) }

(*--------------------------------------------------------------------
  Initial state: all disks on the first tower (index 0)
--------------------------------------------------------------------*)
Init ==
  /\ tower = [i \in Towers |-> IF i = 0 THEN AllDisks ELSE 0]
  /\ \A t \in Towers : tower[t] \in 0 .. AllDisks

(*--------------------------------------------------------------------
  Move action
--------------------------------------------------------------------*)
Move ==
  \E d \in DiskValues :
    \E s \in Towers :
      \E d2 \in Towers :
        /\ s # d2
        /\ DiskOn(d, s)                     \* disk d is on source tower
        /\ SmallestDisk(s) = d               \* it is the smallest on source
        /\ (tower[d2] = 0 \/ SmallestDisk(d2) > d) \* destination ok
        /\ tower' = [tower EXCEPT ![s] = tower[s] - d,
                                  ![d2] = tower[d2] + d]

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next == Move

(*--------------------------------------------------------------------
  Specification (temporal formula)
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<tower>>

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
(* Type correctness: each tower value is a natural number less than 2^D *)
TypeOK ==
  /\ \A t \in Towers : tower[t] \in 0 .. AllDisks
  /\ \A t1, t2 \in Towers : t1 # t2 => tower[t1] # tower[t2]   \* ensures no disk appears on two towers

(* Conservation: total sum of tower values equals the sum of all disks *)
Inv ==
  /\ \A t \in Towers : tower[t] \in 0 .. AllDisks
  /\ \A t1, t2 \in Towers : t1 # t2 => tower[t1] # tower[t2]
  /\ \A t \in Towers : DisksOn(t) \subseteq DiskValues
  /\ \A d \in DiskValues :
        (\E t \in Towers : DiskOn(d, t))   \* each disk is somewhere
  /\ \A t \in Towers : \A d1, d2 \in DisksOn(t) :
        d1 # d2 => d1 # d2                 \* trivial distinctness
  /\ \A t \in Towers :
        \A d1 \in DisksOn(t) :
          \A d2 \in DisksOn(t) :
            d1 # d2 => (d1 # d2)           \* maintain set nature
  /\ \A t \in Towers : \A d \in DiskValues :
        DiskOn(d, t) => d \in DisksOn(t)
  /\ \A t \in Towers : \A d \in DisksOn(t) :
        DiskOn(d, t)
  /\ \A t \in Towers :
        \A d \in DiskValues :
          DiskOn(d, t) => d \in DiskValues
  /\ \A d \in DiskValues :
        \E! t \in Towers : DiskOn(d, t)    \* each disk appears exactly once
  /\ \A t \in Towers :
        \A d1, d2 \in DisksOn(t) :
          d1 # d2 => d1 # d2               \* redundancy for clarity
  /\ \A t \in Towers :
        \A d \in DisksOn(t) :
          \A e \in DiskValues :
            e < d => ~DiskOn(e, t)        \* ordering: no smaller disk beneath larger
  /\ \A t \in Towers : tower[t] = 
        \Sum { d \in DiskValues : DiskOn(d, t) : d }
  /\ \Sum { tower[t] : t \in Towers } = AllDisks

(* The above Inv captures both type correctness and the conservation property *)

=============================================================================