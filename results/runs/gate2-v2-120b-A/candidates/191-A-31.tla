---- MODULE Hanoi ----
EXTENDS Naturals, TLC

(*--------------------------------------------------------------------*)
(*  Constants                                                       *)
(*--------------------------------------------------------------------*)
CONSTANTS D, N

(*--------------------------------------------------------------------*)
(*  Derived constants                                                *)
(*--------------------------------------------------------------------*)
DiskSet == 1 .. D
Towers  == 1 .. N

Disk(d) == 2 ^ (d - 1)            \* size of disk d, a power of two
AllDisks == UNION { Disk(d) : d \in DiskSet }

TotalMask == 2 ^ D - 1           \* sum of all disk values (all bits set)

(*--------------------------------------------------------------------*)
(*  State variable                                                   *)
(*--------------------------------------------------------------------*)
VARIABLES towers

(* towers[t] is the natural number encoding the set of disks on tower t *)

(*--------------------------------------------------------------------*)
(*  Helper definitions                                               *)
(*--------------------------------------------------------------------*)
(* Presence of a particular disk value x in tower t *)
DiskIn(t, x) == (towers[t] / x) % 2 = 1

(* Smallest (i.e., lowest-order) disk present on tower t *)
SmallestDisk(t) ==
  CHOOSE x \in DiskSet :
    /\ DiskIn(t, Disk(x))
    /\ \A y \in DiskSet : y < x => ~DiskIn(t, Disk(y))

(* Whether tower t is empty *)
Empty(t) == towers[t] = 0

(*--------------------------------------------------------------------*)
(*  Initialization                                                   *)
(*--------------------------------------------------------------------*)
Init ==
  /\ towers = [t \in Towers |-> IF t = 1 THEN TotalMask ELSE 0]
  /\ ~EnableStuttering   \* TLC flag to avoid stuttering steps

(*--------------------------------------------------------------------*)
(*  Next-state relation                                              *)
(*--------------------------------------------------------------------*)
Next ==
  \/ \E d \in DiskSet :
        \E src \in Towers :
          \E dst \in Towers :
            /\ src # dst
            /\ DiskIn(src, Disk(d))                     \* disk is on source
            /\ \A y \in DiskSet : y < d => ~DiskIn(src, Disk(y))   \* smallest on source
            /\ (Empty(dst) \/ \A y \in DiskSet : y < d => ~DiskIn(dst, Disk(y))) \* no smaller on dest
            /\ towers' = [t \in Towers |-> 
                  IF t = src THEN towers[t] - Disk(d)
                  ELSE IF t = dst THEN towers[t] + Disk(d)
                  ELSE towers[t]]
  \/ UNCHANGED towers

(*--------------------------------------------------------------------*)
(*  Specification                                                    *)
(*--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<towers>>

(*--------------------------------------------------------------------*)
(*  Safety invariants                                                *)
(*--------------------------------------------------------------------*)
TypeOK ==
  /\ \A t \in Towers : towers[t] \in Nat
  /\ \A t \in Towers : towers[t] < 2 ^ D

TotalMaskInvariant == 
  /\ \A t \in Towers : towers[t] \in 0 .. TotalMask
  /\ \A d \in DiskSet : (Disk(d) # 0) => 
        \E! t \in Towers : DiskIn(t, Disk(d))   \* each disk appears exactly once
  /\ \A t \in Towers : 
        \A d \in DiskSet :
          DiskIn(t, Disk(d)) => 
            \A y \in DiskSet : y < d => ~DiskIn(t, Disk(y))   \* ordering constraint

Inv == TypeOK /\ TotalMaskInvariant

(*--------------------------------------------------------------------*)
(*  The invariants listed in the .cfg file                           *)
(*--------------------------------------------------------------------*)
TypeOKInv == TypeOK
SafetyInv == Inv

=============================================================================