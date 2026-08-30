---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES cells

vars == <<cells>>

Rows == 1..N
Cols == 1..N
Positions == Rows \X Cols

Neighbors == {<<-1, -1>>, <<-1, 0>>, <<-1, 1>>, <<0, -1>>, <<0, 1>>, <<1, -1>>, <<1, 0>>, <<1, 1>>}

Within(p) == p[1] \in Rows /\ p[2] \in Cols

\* A position just outside the grid is treated as dead (value 0) for neighbor
\* counting; positions farther out never arise from a single-step neighbor sum.
ValueAt(p) == IF Within(p) THEN IF cells[p] THEN 1 ELSE 0 ELSE 0

SumLive(p) ==
  LET neigh == {<<p[1] + q[1], p[2] + q[2]>> : q \in Neighbors}
  IN LET count == {q \in neigh : Within(q) /\ cells[q]} IN Cardinality(count)

\* The automaton is deterministic: the next state is a pure function of the
\* current one, so starting from one initial configuration the entire run is
\* fixed and admits no alternative path.
NextCells(p) ==
  IF ValueAt(p) = 1
    THEN (SumLive(p) = 2 \/ SumLive(p) = 3)
    ELSE SumLive(p) = 3

TypeOK == cells \in [Positions -> BOOLEAN]

Init == \E f \in [Positions -> BOOLEAN] : cells = f

Tick == cells' = [p \in Positions |-> NextCells(p)]

Next == Tick

Spec == Init /\ [][Next]_vars

\* Typed so every reachable state can pass model-checking, not a property to
\* assert about the automaton's behavior.
TypeOKInv == TypeOK

====