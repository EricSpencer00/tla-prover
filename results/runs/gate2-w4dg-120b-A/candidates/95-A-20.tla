---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

ASSUME N \in Nat /\ N >= 1

Positions == 1..N

\* The universe of positions inside the grid; outside positions are treated as
\* dead when counting neighbors.
AllPositions == Positions \X Positions

\* The set of positions adjacent to a given position (up to 8, fewer at edges).
Neighbors(p) == { q \in AllPositions : q # p /\ \A k \in {"x", "y"} : |p[k] - q[k]| <= 1 }

VARIABLES alive

vars == << alive >>

\* The neighbor count at position p takes a value of zero for any position q
\* outside the grid, because allPositions is limited to positions 1..N.
AliveNeighbors(p) == Cardinality({q \in Neighbors(p) : alive[q]})

TypeOK == alive \in [AllPositions -> BOOLEAN]

\* Any configuration of the grid is a permissible initial state.
Init == alive = [p \in AllPositions |-> CHOOSE v \in {TRUE, FALSE} : TRUE]

\* Fully deterministic simultaneous update: the next state is a pure function of
\* the current state, applied at every position at once.
Tick ==
  /\ alive' = [p \in AllPositions |->
        LET c == AliveNeighbors(p) IN
          IF alive[p] /\ (c = 2 \/ c = 3) THEN TRUE
          ELSE IF ~alive[p] /\ c = 3 THEN TRUE
          ELSE FALSE]
  /\ UNCHANGED << >>

Next == Tick

Spec == Init /\ [][Next]_vars

====