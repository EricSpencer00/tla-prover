---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

ASSUME D \in Nat /\ D > 0 /\ N \in Nat /\ N > 0

Stacks == 0..(N - 1)

\* Bits of the tower values encode disk presence; bit k is the disk of size 2^k.
Disk(k) == 2 ^ k
HighestDisk == Disk(D - 1)

RECURSIVE SumFn(_, _)
SumFn(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumFn(f, S \ {x})

VARIABLES value

vars == <<value>>

\* The three-locality condition varies with the source: it always tests the
\* destination tower's lower bits, but the source tower's lower bits only
\* matter when the disk actually moves from that tower (source = x).
TopOn(t) == CHOOSE k \in 0..(D - 1) : (value[t] \land Disk(k)) = Disk(k)

TypeOK ==
  /\ value \in [Stacks -> Nat]
  /\ \A t \in Stacks : value[t] < 2 ^ D

Init ==
  /\ value = [t \in Stacks |-> IF t = 0 THEN 2 ^ D - 1 ELSE 0]
  /\ TRUE

\* Move a disk that is the smallest on its source tower, and only onto
\* an empty destination or one whose smallest disk is larger.
Move(d, src, dst) ==
  /\ src # dst
  /\ (value[src] \land d) = d
  /\ (value[src] \land (d - 1)) = 0
  /\ (value[dst] = 0 \/ (value[dst] \land (d - 1)) = 0)
  /\ value' = [value EXCEPT ![src] = @ - d, ![dst] = @ + d]

Moves ==
  \E d \in {Disk(k) : k \in 0..(D - 1)}, src \in Stacks, dst \in Stacks : Move(d, src, dst)

Next ==
  /\ Moves
  /\ TRUE

\* Conservation: the tower values are a partition of the full disk set.
Inv ==
  /\ SumFn(value, Stacks) = 2 ^ D - 1
  /\ TypeOK

Spec == Init /\ [][Next]_vars

====