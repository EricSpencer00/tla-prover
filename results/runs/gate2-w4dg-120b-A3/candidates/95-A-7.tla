---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANTS N

Cells == {1 .. N} \X {1 .. N}

VARIABLES alive

vars == <<alive>>

NeighbourOffsets == {
  <<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
  <<0, -1>>,           <<0, 1>>,
  <<1, -1>>,  <<1, 0>>, <<1, 1>>
}

\* The eight neighboring cells of position p that lie inside the grid.
NLive(p) ==
  Cardinality({
    q \in Cells :
      \E d \in NeighbourOffsets :
        q = <<p[1] + d[1], p[2] + d[2]>> /\ alive[q]
  })

Init ==
  /\ alive \in [Cells -> BOOLEAN]

Tick ==
  /\ alive' = [p \in Cells |-> IF alive[p]
                    THEN (NLive(p) = 2 \/ NLive(p) = 3)
                    ELSE (NLive(p) = 3)]
  /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK == alive \in [Cells -> BOOLEAN]

====