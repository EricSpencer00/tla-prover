---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, TLC

(*
  Tower of Hanoi specification using a bitwise representation of disk positions.
  Disks are powers of two: 1,2,4,...,2^(D-1).
  There are N towers, numbered 0..N-1.
*)

CONSTANTS D, N

\* --- Derived constants -------------------------------------------------
DiskValues == { 2 ^ i : i \in 0..(D - 1) }

MaxMask == 2 ^ D - 1          \* Bitmask with all D bits set

Towers == 0..(N - 1)          \* Set of tower indices

\* --- Variables ---------------------------------------------------------
VARIABLES towers

\* towers[t] is a natural number encoding the set of disks on tower t
\* The binary representation of towers[t] has bit i set iff disk 2^i is on tower t.

\* Helper to extract the smallest disk present on a tower (or 0 if empty)
SmallestDisk(t) ==
  IF towers[t] = 0
    THEN 0
    ELSE
      LET bits == { i \in 0..(D - 1) : (towers[t] DIV 2 ^ i) % 2 = 1 } IN
        2 ^ (Min(bits))

\* --- Initial state ------------------------------------------------------
Init ==
  /\ towers = [t \in Towers |-> IF t = 0 THEN MaxMask ELSE 0]
  /\ /\ /\

\* --- Move action ---------------------------------------------------------
Move ==
  \E src \in Towers, dst \in Towers :
    /\ src # dst
    /\ /\ \* The source tower must contain at least one disk
          towers[src] # 0
        /\ \* Determine the smallest disk on the source tower
          LET d == SmallestDisk(src) IN
             /\ d # 0
             /\ \* Destination must not have any smaller disk
                (towers[dst] = 0 \/ (towers[dst] DIV d) % 2 = 0)
             /\ \* Perform the move
                /\ towers' = [t \in Towers |
                               IF t = src
                                 THEN towers[t] - d
                                 ELSE IF t = dst
                                        THEN towers[t] + d
                                        ELSE towers[t]]
    /\ UNCHANGED << >>

\* --- Next-state relation -------------------------------------------------
Next == Move

\* --- Specification --------------------------------------------------------
Spec == Init /\ [][Next]_<<towers>>

\* --- Type correctness invariant ------------------------------------------
TypeOK ==
  /\ towers \in [Towers -> 0..MaxMask]
  /\ \A t \in Towers : towers[t] <= MaxMask

\* --- Safety invariant (conservation of all disks) ------------------------
Inv ==
  /\ \A t \in Towers : towers[t] <= MaxMask
  /\ \A t \in Towers : towers[t] >= 0
  /\ \A t1, t2 \in Towers : (t1 # t2) => (towers[t1] * towers[t2]) = 0
        \* This ensures no disk appears on two towers simultaneously
  /\ Sum(towers) = MaxMask

\* Sum of all tower values
Sum(t) == \Sum_{i \in DOMAIN t} t[i]

\* --- THEOREM (optional, can be omitted) ---------------------------------
\* THEOREM Spec => []Inv

====