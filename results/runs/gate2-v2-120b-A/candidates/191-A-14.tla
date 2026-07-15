---- MODULE Hanoi ----
EXTENDS Naturals, TLC

(* --constants-- *)
CONSTANT D \* number of disks
CONSTANT N \* number of towers

(* --derived constants-- *)
DiskSet == 1 .. (2 ^ D - 1) \* all possible bit masks for individual disks
Towers == 1 .. N

(* --variables-- *)
VARIABLES towers

(* --type definitions-- *)
Disks == { 2 ^ i : i \in 0 .. (D - 1) }

(* --initial state-- *)
Init ==
    /\ towers = [i \in Towers |-> IF i = 1 THEN (2 ^ D - 1) ELSE 0]
    /\ TypeOK

(* --helper definitions-- *)
DiskInTower(t, d) == (t \in Towers) /\ (d \in Disks) /\ ((towers[t] \& d) = d)

SmallestOn(t) ==
    \E d \in Disks :
        /\ DiskInTower(t, d)
        /\ \A d2 \in Disks :
               (d2 < d) => ~DiskInTower(t, d2)

(* Bitwise AND defined using arithmetic: a & b = Sum_{i} 2^i when both a and b have bit i set *)
BitAnd(a, b) ==
    \* Set of positions where both a and b have a 1 bit
    LET bits == { i \in 0 .. (D - 1) : ((a \div 2^i) % 2 = 1) /\ ((b \div 2^i) % 2 = 1) } IN
    Sum({ 2 ^ i : i \in bits })

(* --move action-- *)
Move ==
    \E src \in Towers, dst \in Towers, d \in Disks :
        /\ src # dst
        /\ DiskInTower(src, d)               \* disk d is present on source
        /\ SmallestOn(src)                   \* d is the smallest disk on source
        /\ (towers[dst] = 0 \/ 
            \A d2 \in Disks :
                (d2 < d) => ~DiskInTower(dst, d2))   \* no smaller disk on destination
        /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                                   ![dst] = towers[dst] + d]

Next == Move

(* --type correctness invariant-- *)
TypeOK ==
    /\ towers \in [Towers -> Nat]
    /\ \A t \in Towers : towers[t] < 2 ^ D

(* --safety invariant (conservation)-- *)
Inv ==
    /\ towers[1] + towers[2] + ... + towers[N] = 2 ^ D - 1
    /\ \A t \in Towers : towers[t] \in Nat
    /\ TypeOK

(* --specification definition-- *)
Spec == Init /\ [][Next]_towers

(* --theorem (optional, for readability)--
THEOREM Spec => []Inv
*)

====