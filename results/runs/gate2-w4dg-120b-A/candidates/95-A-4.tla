---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

\* A grid position is an integer pair (r, c) within the N-by-N square.
Positions == {p \in (1..N) \X (1..N) : TRUE}

\* Neighborhood offsets: the eight cells surrounding a position, plus (0,0) for later convenience.
Offsets == {o \in (-1..1) \X (-1..1) : o # <<0, 0>>}

\* NeighborSum counts live cells around a position, treating anything outside the
\* grid as dead (value zero) as required.
NeighborSum(A, p) == LET
    f[S \in SUBSET Positions] ==
        IF S = {} THEN 0
        ELSE LET q == CHOOSE x \in S : TRUE IN A[q] + f[S \ {q}]
    IN
        f[{q \in Positions : Cardinality({o \in Offsets : q + o = p}) = 1}]

VARIABLES cells

vars == <<cells>>

TypeOK == cells \in [Positions -> BOOLEAN]

Init ==
    /\ cells \in [Positions -> BOOLEAN]
    /\ Cardinality({p \in Positions : cells[p] = TRUE}) = Cardinality(Positions)

\* The update is deterministic: every cell is recomputed together from the same snapshot of
\* the current grid. The rule matches Conway's Life exactly.
Tick ==
    /\ cells' = [p \in Positions |-> LET k == NeighborSum(cells, p) IN
                    IF cells[p] THEN (k = 2 \/ k = 3) ELSE (k = 3)]
    /\ UNCHANGED N

Next == Tick

Spec == Init /\ [][Next]_vars

====