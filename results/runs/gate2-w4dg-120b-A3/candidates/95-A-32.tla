---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N > 0

Positions == {p \in (1..N) \X (1..N)}

RECURSIVE NeighborsOf(_)
NeighborsOf(p) ==
  {q \in Positions : q # p /\ 
     LEN({k \in 1..2 : p[k] = q[k]}) >= 1 /\ 
     \A k \in 1..2 : ABS(p[k] - q[k]) <= 1}

INBOUND(p) == p \in Positions

VARIABLES cells
vars == <<cells>>

\* Each cell is alive (TRUE) or dead (FALSE).  Any configuration is
\* reachable at init time, so the starting generation is nondeterministic.
Init ==
  /\ cells \in [Positions -> BOOLEAN]

\* The Game of Life: every cell is updated from the same old generation.
Update ==
  /\ cells' = [p \in Positions |->
        LET alive == cells[p]
            liveNbrs == Cardinality({q \in NeighborsOf(p) : cells[q]})
        IN IF alive /\ (liveNbrs = 2 \/ liveNbrs = 3) THEN TRUE
              ELSE IF ~alive /\ liveNbrs = 3 THEN TRUE
              ELSE FALSE]

Next == Update

Spec == Init /\ [][Next]_vars

TypeOK == cells \in [Positions -> BOOLEAN]

====