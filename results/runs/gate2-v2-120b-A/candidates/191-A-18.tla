---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Constants (set in the .cfg file)
-----------------------------------------------------------------*)
CONSTANT D \* number of disks
CONSTANT N \* number of towers

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
DiskVals == { 2^k : k \in 0..(D - 1) }
ALLDISKS == 2^D - 1

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES towers

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
(* towers[i] is the natural number encoding the set of disks on tower i *)
Tower(i) == towers[i]

(* The set of disks currently on tower i, derived from its bitmask *)
DisksOn(i) == { d \in DiskVals : (Tower(i) \* 1) % (2 * d) >= d }

(* The smallest disk on tower i, if any *)
SmallestDisk(i) ==
  IF Tower(i) = 0 THEN 0
  ELSE
    CHOOSE d \in DiskVals :
      /\ (Tower(i) % (2 * d) >= d)      \* disk d is present
      /\ \A e \in DiskVals : (e < d) => (Tower(i) % (2 * e) < e) \* no smaller disk present

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN ALLDISKS ELSE 0]
  /\ TypeOK

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
Move(src, dst) ==
  /\ src \in 1..N
  /\ dst \in 1..N
  /\ src # dst
  /\ Tower(src) # 0
  /\ LET d == SmallestDisk(src) IN
       /\ d # 0
       /\ (Tower(dst) = 0 \/ d < SmallestDisk(dst))
       /\ towers' = [towers EXCEPT ![src] = Tower(src) - d,
                                ![dst] = Tower(dst) + d]

Next ==
  \E src, dst \in 1..N: Move(src, dst)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<towers>>

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
(* Type correctness: each tower value is a natural number less than 2^D *)
TypeOK ==
  /\ \A i \in 1..N: towers[i] \in Nat
  /\ \A i \in 1..N: towers[i] < 2^D

(* Conservation of all disks *)
Inv ==
  /\ \A i \in 1..N: towers[i] \in Nat
  /\ Sum(i \in 1..N) towers[i] = ALLDISKS

=================================