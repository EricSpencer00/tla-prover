---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

(* Set of all disk values (powers of two) *)
DiskValues == { 2 ^ k : k \in 0..(D - 1) }

IsPowerOfTwo(d) == d \in DiskValues

(* True iff disk d (a power of two) is present on tower value t *)
DiskPresent(t, d) == ((t \div d) mod 2) = 1

(* True iff d is the smallest disk on tower value t *)
SmallestOn(t, d) ==
    DiskPresent(t, d) /\ (t mod d) = 0

(* ----------------------------------------------------------------------
   Initialization
   ---------------------------------------------------------------------- *)

Init ==
    /\ towers[1] = (2 ^ D) - 1
    /\ \A i \in 2..N: towers[i] = 0

(* ----------------------------------------------------------------------
   Next-state relation (a legal move)
   ---------------------------------------------------------------------- *)

Next ==
    \E i \in 1..N:
      \E j \in 1..N:
        /\ i # j
        /\ \E d \in DiskValues:
            /\ SmallestOn(towers[i], d)          \* disk d is smallest on source
            /\ (towers[j] mod d) = 0              \* no smaller disk on dest
            /\ towers' = [towers EXCEPT
                            ![i] = towers[i] - d,
                            ![j] = towers[j] + d]

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec ==
    Init /\ [][Next]_towers

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)

(* Type correctness: each tower stores a natural number less than 2^D *)
TypeOK ==
    \A i \in 1..N: towers[i] \in Nat /\ towers[i] < (2 ^ D)

(* Conservation of total disk value *)
Inv ==
    Sum({ towers[i] : i \in 1..N }) = (2 ^ D) - 1

(* ----------------------------------------------------------------------
   Theorems
   ---------------------------------------------------------------------- *)

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv

====