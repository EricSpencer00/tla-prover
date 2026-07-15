---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, TLC

(* 
   Constants (set in the .cfg file)
*)
CONSTANT D
CONSTANT N

(* Derived constant: total sum of all disk values, i.e., 2^D - 1 *)
Total == 2 ^ D - 1

(* The set of towers, indexed 1..N *)
Towers == 1..N

(* 
   The set of disks, represented as powers of two.
   Disk k has size 2^k, where k ranges from 0 to D-1.
*)
Disks == { 2 ^ k : k \in 0..(D - 1) }

(* Helper to compute the smallest (least significant) disk present in a tower value *)
SmallestDisk(v) == 
    IF v = 0 THEN 0
    ELSE 2 ^ (NatLog2(v))

(* NatLog2 returns the exponent of the least significant set bit in a positive integer.
   For v > 0, v = 2^e + rest where rest < 2^e. The function yields e. *)
NatLog2(v) == 
    IF v = 0 THEN 0
    ELSE
        LET e == 0 IN
        WHILE (2 ^ (e + 1)) <= v DO e := e + 1 END ;
        IF (v % (2 ^ (e + 1))) = 0 THEN e + 1 ELSE e

(* TypeOK ensures each tower value is a natural number less than 2^D *)
TypeOK == /\ \A i \in Towers: towers[i] \in Nat
          /\ \A i \in Towers: towers[i] < 2 ^ D

VARIABLES towers

(* Initial state: all disks on tower 1, others empty *)
Init == 
    /\ towers = [i \in Towers |-> IF i = 1 THEN Total ELSE 0]
    /\ TypeOK

(* 
   Move(d, src, dst) performs a legal move of disk d from src to dst.
   It updates the towers array accordingly.
*)
Move(d, src, dst) == 
    /\ towers' = [t \in Towers |-> 
          IF t = src THEN towers[t] - d
          ELSE IF t = dst THEN towers[t] + d
          ELSE towers[t]]
    /\ UNCHANGED << >>

(* Next-state relation: nondeterministically choose a legal move *)
Next == 
    \E d \in Disks:
      \E src \in Towers:
        \E dst \in Towers:
          /\ src # dst
          /\ (towers[src] # 0)                     \* source not empty
          /\ (towers[src] % (2 * d)) = d           \* d is the smallest disk on src
          /\ ((towers[dst] = 0) \/ (towers[dst] % (2 * d)) = 0)  \* dst empty or its smallest disk larger than d
          /\ Move(d, src, dst)

(* Safety invariant: conservation of total disk value *)
Inv == /\ \A i \in Towers: towers[i] \in Nat
       /\ \A i \in Towers: towers[i] < 2 ^ D
       /\ \Sum i \in Towers: towers[i] = Total

Spec == Init /\ [][Next]_<<towers>>

====