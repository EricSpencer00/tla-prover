---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS D, N
ASSUME D \in Nat \ {0} /\ N \in Nat \ {0}

\* Bit value for each disk (powers of two)
DISKS == { 2^k : k \in 0..(D-1) }

\* All possible tower indices
TOWERS == 1..N

\* The initial tower configuration: all disks on tower 1, others empty
InitTowers == [t \in TOWERS |-> IF t = 1 THEN 2^D - 1 ELSE 0]

VARIABLES towers

\* Type correctness: each tower value is a natural number < 2^D
TypeOK == towers \in [TOWERS -> Nat] /\ \A t \in TOWERS: towers[t] < 2^D

\* Conservation: the sum of all tower values equals 2^D - 1
Inv == Sum(t \in TOWERS) towers[t] = 2^D - 1

\* Helper: bitwise AND of two numbers (pure TLA+ implementation)
\* This function returns the common bits set in both operands
\* It works because disk values are powers of two.
\* The implementation uses repeated subtraction to test membership.
AND(a, b) ==
  IF a = 0 \/ b = 0 THEN 0
  ELSE IF a % 2 = 0 THEN AND(a DIV 2, b) * 2
  ELSE IF b % 2 = 0 THEN AND(a, b DIV 2) * 2
  ELSE 1

\* The actual move action: pick a source, destination, and a disk
Move ==
  \E src, dst \in TOWERS, d \in DISKS :
    /\ src # dst
    /\ towers[src] % d = d                \* disk d present on src
    /\ towers[src] % (2*d) = 0             \* d is the smallest on src
    /\ towers[dst] % d = 0                \* no smaller disk on dst
    /\ towers' = [t \in TOWERS |-> IF t = src THEN towers[t] - d
                                            ELSE IF t = dst THEN towers[t] + d
                                            ELSE towers[t]]

Init == towers = InitTowers

Next == Move

Spec == Init /\ [][Next]_towers

\* The safety invariants required by the configuration
\* TypeOK and Inv are already defined above
INVARIANTS TypeOK, Inv

====