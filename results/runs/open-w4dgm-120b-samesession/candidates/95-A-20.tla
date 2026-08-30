---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N

\* The grid is an N-by-N square. Each position maps to a boolean: TRUE means
\* "alive", FALSE means "dead". Cells outside the grid are treated as dead
\* when counting neighbors (the "bounded" aspect of the spec).
VARIABLES alive

vars == <<alive>>

Positions == 1..N

TypeOK ==
  /\ alive \in [Positions \X Positions -> BOOLEAN]

Init ==
  \E a \in [Positions \X Positions -> BOOLEAN] : alive = a

\* The neighbor-counting helper. The grid is bounded: only positions inside
\* the N-by-N square contribute; positions outside are simply absent.
LiveNeighbors(p) ==
  Cardinality(
    {q \in Positions \X Positions :
        q # p /\ alive[q] /\ (q[1] - p[1])^2 + (q[2] - p[2])^2 <= 2}
  )

\* The tick fires on the whole grid simultaneously, computed from the
\* current generation's neighbor counts. The update is deterministic given
\* the current generation: any two runs starting from the same grid stay
\* identical from that point onward.
Tick ==
  /\ \E a \in [Positions \X Positions -> BOOLEAN] :
       \A p \in Positions \X Positions :
         a[p] = (IF alive[p] /\ LiveNeighbors(p) \in 2..3 THEN TRUE
                 ELSE IF ~alive[p] /\ LiveNeighbors(p) = 3 THEN TRUE
                 ELSE FALSE)
  /\ alive' = a

Next == Tick

Spec == Init /\ [][Next]_vars

\* The only required invariant is that the state variable stays a total
\* mapping on the grid (a boolean at every position) -- essentially a
\* type-check on the whole reachable-state set.
TypeOKInv == TypeOK

====