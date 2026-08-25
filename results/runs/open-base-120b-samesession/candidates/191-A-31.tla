---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS D, N

VARIABLES towers

(*-----------------------------------------------------------------
  DiskSet : the set of all disk sizes, each a power of two.
-----------------------------------------------------------------*)
DiskSet == { 2^i : i \in 0..D-1 }

(*-----------------------------------------------------------------
  Has(v, d)  : true iff disk d (a power of two) is present in tower v.
  The test uses the remainder modulo 2*d.
-----------------------------------------------------------------*)
Has(v, d) == (v % (2 * d) >= d)

(*-----------------------------------------------------------------
  IsSmallest(v, d) : d is present in v and no smaller disk is present.
-----------------------------------------------------------------*)
IsSmallest(v, d) == 
    /\ Has(v, d)
    /\ \A e \in DiskSet : e < d => ~Has(v, e)

(*-----------------------------------------------------------------
  NoSmaller(v, d) : tower v contains no disk smaller than d.
-----------------------------------------------------------------*)
NoSmaller(v, d) ==
    \A e \in DiskSet : e < d => ~Has(v, e)

(*-----------------------------------------------------------------
  Type correctness: each tower value is a natural < 2^D.
-----------------------------------------------------------------*)
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] >= 0 /\ towers[i] < 2^D

(*-----------------------------------------------------------------
  Conservation invariant: total of all disks is 2^D - 1.
-----------------------------------------------------------------*)
Inv ==
    /\ \Sum i \in 1..N : towers[i] = 2^D - 1

(*-----------------------------------------------------------------
  Initial state: all disks on the first tower, others empty.
-----------------------------------------------------------------*)
Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN (2^D - 1) ELSE 0]
    /\ TypeOK

(*-----------------------------------------------------------------
  A legal move of a single smallest disk from src to dst.
-----------------------------------------------------------------*)
Move ==
    \E d \in DiskSet :
        \E src \in 1..N :
            \E dst \in 1..N :
                /\ src # dst
                /\ Has(towers[src], d)
                /\ IsSmallest(towers[src], d)
                /\ NoSmaller(towers[dst], d)
                /\ towers' = [i \in 1..N |-> 
                        IF i = src THEN towers[i] - d
                        ELSE IF i = dst THEN towers[i] + d
                        ELSE towers[i]]

Next == Move

(*-----------------------------------------------------------------
  Specification: init and always-step.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<towers>>

====