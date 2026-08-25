---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT D
CONSTANT N

\* ----------------------------------------------------------------------
\* Derived definitions
\* ----------------------------------------------------------------------
DiskVal(k) == 2 ^ (k - 1)                \* size of disk k (k = 1..D)
AllDisks == (2 ^ D) - 1                  \* sum of all disk values
Tower == 1 .. N

\* ----------------------------------------------------------------------
\* State variable
\* ----------------------------------------------------------------------
VARIABLE towers

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ towers \in [Tower -> Nat]
  /\ towers[1] = AllDisks
  /\ \A i \in Tower \ {1} : towers[i] = 0

\* ----------------------------------------------------------------------
\* Move action
\* ----------------------------------------------------------------------
Move ==
  \E source, dest \in Tower :
    /\ source # dest
    /\ \E k \in 1 .. D :
         LET d == DiskVal(k) IN
           /\ (towers[source] % (2 * d)) = d           \* disk d is present on source
           /\ (towers[source] % d) = 0                \* no smaller disk on source
           /\ (towers[dest] % d) = 0                  \* no smaller disk on dest
           /\ towers' = [towers EXCEPT
                           ![source] = towers[source] - d,
                           ![dest]   = towers[dest]   + d]

Next == Move

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_towers

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ towers \in [Tower -> Nat]
  /\ \A i \in Tower : towers[i] < 2 ^ D

\* ----------------------------------------------------------------------
\* Helper: sum of a finite set of natural numbers
\* ----------------------------------------------------------------------
RECURSIVE SumSet(_)

SumSet(S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE y \in S : TRUE IN
      x + SumSet(S \ {x})

\* ----------------------------------------------------------------------
\* Conservation invariant
\* ----------------------------------------------------------------------
Inv ==
  SumSet({ towers[i] : i \in Tower }) = AllDisks

====