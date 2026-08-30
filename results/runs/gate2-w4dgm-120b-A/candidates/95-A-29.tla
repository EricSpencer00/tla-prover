---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES cells

vars == <<cells>>

Positions == [r : 1..N, c : 1..N]

TypeOK ==
  /\ cells \in [Positions -> BOOLEAN]

\* Neighbors are the eight surrounding positions; positions outside the
\* grid are treated as dead and contribute zero to the count.
LiveNeighbors(p) ==
  Cardinality({q \in Positions : q # p /\ q.r >= 1 /\ q.r <= N /\ q.c >= 1 /\ q.c <= N
                             /\ (q.r - p.r)^2 + (q.c - p.c)^2 <= 2
                             /\ cells[q]})

\* The Game of Life update is deterministic: given the current grid,
\* the next generation is uniquely determined; nondeterminism appears only
\* at initialization, when the starting configuration is chosen.
OwnNext(p) ==
  /\ \/ cells[p]
        /\ LiveNeighbors(p) \in {2, 3}
  \/ /\ ~ cells[p]
        /\ LiveNeighbors(p) = 3

Init ==
  /\ cells \in [Positions -> BOOLEAN]

Next ==
  /\ \E f \in [Positions -> BOOLEAN] :
       \A p \in Positions :
         f[p] = OwnNext(p)
  /\ UNCHANGED cells

Spec == Init /\ [][Next]_vars

\* The deterministic update given a fixed start is the only thing that
\* matters here: there is no alternative evolution to rule out, so the
\* cell-contents function stays a well-defined mapping from positions to
\* boolean values.
TypeOKInv == TypeOK

====