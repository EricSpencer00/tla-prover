---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES alive

vars == <<alive>>

Positions == 1..N

OnGrid(r, c) == r \in Positions /\ c \in Positions

Neighbors == {<<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
              <<0, -1>>,            <<0, 1>>,
              <<1, -1>>,  <<1, 0>>, <<1, 1>>}

TypeOK == alive \in [Positions \X Positions -> BOOLEAN]

Init == \E f \in [Positions \X Positions -> BOOLEAN] : alive = f

LiveNeighbors(r, c) ==
  Cardinality({d \in Neighbors : OnGrid(r + d[1], c + d[2]) /\ alive[r + d[1], c + d[2]]})

Tick ==
  alive' = [p \in Positions \X Positions |->
              let cnt == LiveNeighbors(p[1], p[2]) in
                IF alive[p] /\ cnt \in {2, 3} THEN TRUE
                ELSE IF ~alive[p] /\ cnt = 3 THEN TRUE
                ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

====