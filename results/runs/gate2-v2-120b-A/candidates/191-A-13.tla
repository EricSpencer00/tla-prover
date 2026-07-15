---- MODULE Hanoi ----
EXTENDS Naturals, TLC

CONSTANTS D, N

(* Disk sizes are powers of two: 2^k for k = 0..D-1 *)
DiskSet == { 2 ^ k : k \in 0..(D - 1) }

(* The set of possible tower indices *)
Tower == 1..N

(* Helper: the sum of all disks, i.e., 2^D - 1 *)
AllDisks == 2 ^ D - 1

VARIABLES towers

(* towers[t] is the natural number encoding the set of disks on tower t *)
(* The collection of tower values is represented as a function from Tower to Nat *)
vars == << towers >>

Init ==
    /\ towers = [t \in Tower |-> IF t = 1 THEN AllDisks ELSE 0]
    /\ /\ \A t \in Tower: towers[t] \in 0..AllDisks
       /\ \A t1, t2 \in Tower: t1 # t2 => towers[t1] # towers[t2] \/ towers[t1] = 0 \/ towers[t2] = 0
    /\ \A t \in Tower: towers[t] = 0 \/ 
          \A k \in 0..(D-1):
            LET d == 2^k IN
            ( d \in towers[t] ) => 
               \A j \in 0..(k-1): (2^j) \notin towers[t]

(* Convert a tower's numeric encoding to the set of disks it contains *)
TowerSet(t) == { d \in DiskSet : (towers[t] /\ d) = d }

(* The smallest disk on a tower, or NULL if the tower is empty *)
Smallest(t) ==
    IF towers[t] = 0 THEN NULL
    ELSE
        CHOOSE d \in DiskSet :
            (towers[t] /\ d) = d /\ 
            \A d2 \in DiskSet : (d2 < d) => (towers[t] /\ d2) # d2

Move ==
    \E src \in Tower, dst \in Tower :
        /\ src # dst
        /\ towers[src] # 0
        /\ LET d == Smallest(src) IN
           /\ d # NULL
           /\ (towers[dst] = 0) \/ 
              ( \A d2 \in DiskSet :
                    (d2 # d) /\ ((towers[dst] /\ d2) = d2) => d2 > d )
           /\ towers' = [t \in Tower |-> 
                IF t = src THEN towers[t] - d
                ELSE IF t = dst THEN towers[t] + d
                ELSE towers[t]]

Next == Move

Spec == Init /\ [][Next]_vars

(* Safety property: the total weight of all towers is conserved *)
Conservation == 
    /\ towers[1] + towers[2] + ... + towers[N] = AllDisks

(* Type correctness: each tower value is a natural number less than 2^D *)
TypeOK ==
    /\ \A t \in Tower: towers[t] \in 0..AllDisks
    /\ \A t \in Tower: 
        \A k \in 0..(D-1):
            LET d == 2^k IN
            ( (towers[t] /\ d) = d ) => 
                \A j \in 0..(k-1): ( (towers[t] /\ (2^j)) # (2^j) )

Inv == Conservation /\ TypeOK

====