---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANTS N

VARIABLES A
vars == <<A>>

Positions == 1..N

InBounds(r, c) == r \in Positions /\ c \in Positions

Neighbors == {[dr, dc] \in {-1, 0, 1} \X {-1, 0, 1} : ~(dr = 0 /\ dc = 0)}

LiveNeighbors(r, c) ==
  LET alive(at) == IF at \in Positions \X Positions THEN A[at] ELSE FALSE
  IN Cardinality({p \in Neighbors : alive([r + p[1], c + p[2]])})

TypeOK ==
  /\ A \in [Positions \X Positions -> BOOLEAN]

Init ==
  /\ A \in [Positions \X Positions -> BOOLEAN]

Tick ==
  /\ A' = [rc \in Positions \X Positions |-> IF A[rc] THEN (LiveNeighbors(rc[1], rc[2]) \in {2, 3}) ELSE (LiveNeighbors(rc[1], rc[2]) = 3)]

Next == Tick

Spec == Init /\ [][Next]_vars

====