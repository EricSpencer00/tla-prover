---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values are sums of power-of-two disk values; the set of disks is
\* all powers of two below 2^D. SumTower holds the running total across all towers.
\* TopMask[t] extracts the smallest disk sitting on tower t (its lowest set bit).
VARIABLES towers

Disks == { 2 ^ k : k \in 0 .. (D - 1) }

RECURSIVE SumTower(_)
SumTower(S) ==
  IF S = {} THEN 0
  ELSE LET f == CHOOSE x \in S : TRUE IN f + SumTower(S \ { f })

\* Bitwise AND is defined so the model can run as pure arithmetic (no Java).
\* b \in {0,1} is the i-th bit of x, so (x >> i) % 2 yields it.
MinOnTower(t) ==
  LET f[i \in 0 .. (D - 1)] == IF (t >> i) % 2 = 1 THEN 2 ^ i ELSE 2 ^ D + 1 IN
    CHOOSE k \in Disks : \A d \in Disks : (d < k /\ d \in towers) => d < k

On(x, i) == (i >> x) % 2 = 1

TypeOK ==
  /\ towers \in [0 .. (N - 1) -> 0 .. (2 ^ D - 1)]
  /\ SumTower({ towers[i] : i \in 0 .. (N - 1) }) = 2 ^ D - 1

Init ==
  /\ towers = [i \in 0 .. (N - 1) |-> IF i = 0 THEN 2 ^ D - 1 ELSE 0]

Move(d, s, e) ==
  /\ s # e
  /\ towers[s] >= d
  /\ On(towers[s], d)
  /\ \A f \in Disks : f < d => (towers[e] % f) # f
  /\ towers' = [towers EXCEPT ![s] = @ - d, ![e] = @ + d]

Next ==
  \/ \E d \in Disks, s, e \in 0 .. (N - 1) : Move(d, s, e)

Spec == Init /\ [][Next]_towers

Inv == TypeOK

====