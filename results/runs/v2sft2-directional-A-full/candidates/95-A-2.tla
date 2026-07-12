---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

VARIABLES Cells

Rows == 1..N
Cols == 1..N
Positions == [r \in Rows, c \in Cols]

Offsets == { [dr |-> dr, dc |-> dc] :
                dr \in {-1, 0, 1} /\ dc \in {-1, 0, 1} /\ (dr \# 0 \/ dc \# 0) }

Neighbors(pos) ==
    { [r |-> pos.r + o.dr, c |-> pos.c + o.dc] :
        o \in Offsets /\ (pos.r + o.dr \in Rows) /\ (pos.c + o.dc \in Cols) }

LiveNeighbors(pos) ==
    Cardinality({ q \in Neighbors(pos) : Cells[q] })

Survives(pos) ==
    Cells[pos] /\ (LiveNeighbors(pos) = 2 \/ LiveNeighbors(pos) = 3)

Birthed(pos) ==
    ~Cells[pos] /\ (LiveNeighbors(pos) = 3)

CellUpdate(pos) ==
    Survives(pos) \/ Birthed(pos)

Init ==
    Cells \in [Positions -> BOOLEAN]

Next ==
    Cells' = [pos \in Positions |-> CellUpdate(pos)]

Spec ==
    Init /\ [][Next]_Cells

TypeOK ==
    Cells \in [Positions -> BOOLEAN]

====