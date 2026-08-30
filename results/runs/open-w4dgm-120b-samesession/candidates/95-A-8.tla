---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANTS N

VARIABLES alive
vars == <<alive>>

Positions == 1..N

\* A cell outside the grid boundary is treated as permanently dead, so its
\* neighbor count contribution is always zero.
Outside == "outside"

\* A cell's eight neighboring positions on the grid, filtered to the live
\* cells inside the grid. Outside positions are folded into a dummy cell
\* that carries the value FALSE (dead), so neighbor counting stays uniform.
Neighbors(p) ==
  let deltas == {{-1, -1}, {-1, 0}, {-1, 1},
                 { 0, -1},          { 0, 1},
                 { 1, -1}, { 1, 0}, { 1, 1}} in
  { IF dr \in Positions /\ dc \in Positions
        THEN <<dr, dc>>
        ELSE Outside
    : \E d \in deltas :
        LET dr == p[1] + d[1]
            dc == p[2] + d[2]
        IN TRUE }

Alive(p) == IF p = Outside THEN FALSE ELSE alive[p]

CountLive(p) == Cardinality({q \in Neighbors(p) : Alive(q)})

Init ==
  /\ alive \in [Positions \X Positions -> BOOLEAN]

Tick ==
  /\ alive' = [p \in Positions \X Positions |-> IF alive[p]
                    THEN CountLive(p) \in {2, 3}
                    ELSE CountLive(p) = 3]

Spec == Init /\ [][Tick]_vars

TypeOK == alive \in [Positions \X Positions -> BOOLEAN]

====