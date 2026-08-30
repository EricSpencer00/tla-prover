---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES cells
vars == <<cells>>

Init == \E init \in [1..N -> 1..N -> BOOLEAN] : cells = init

NeighborCount(r, c) ==
  LET pts == {<<p.q, p.r>> : p \in [{q | q \in {-1, 0, 1}} \X {r | r \in {-1, 0, 1}}] : ~(p.q = 0 /\ p.r = 0)} IN
  Cardinality({p \in pts : LET rr == r + p[1] IN LET cc == c + p[2] IN rr \in 1..N /\ cc \in 1..N /\ cells[rr, cc]})

Survives(r, c) == cells[r, c] /\ (NeighborCount(r, c) = 2 \/ NeighborCount(r, c) = 3)
Born(r, c) == ~cells[r, c] /\ NeighborCount(r, c) = 3

Tick ==
  /\ \A r \in 1..N, c \in 1..N : cells' = [cells EXCEPT ![r, c] = Survives(r, c) \/ Born(r, c)]
  /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK == cells \in [1..N -> 1..N -> BOOLEAN]
====