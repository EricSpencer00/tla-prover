---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N

(* --algorithm GameOfLife does not use the algorithmic notation; we model with actions. *)

VARIABLES A

(* --definition of the set of grid positions *)
Pos == 1..N

(* --definition of the set of all coordinates in the grid *)
Coords == Pos \X Pos

(* --initial state: each cell is nondeterministically alive or dead *)
Init ==
    /\ A \in [Coords -> BOOLEAN]

(* --helper to compute the neighbors of a coordinate, staying within the grid *)
Neighbors(p) ==
    LET x == p[1], y == p[2] IN
    { <<i, j>> : i \in Pos, j \in Pos,
        i # x \/ j # y,
        i \in x-1 .. x+1,
        j \in y-1 .. y+1 }

(* --count of live neighbors for a cell at coordinate p *)
LiveNeighborsCount(p) ==
    Cardinality({ q \in Neighbors(p) : A[q] })

(* --deterministic update rule for a single cell *)
UpdateCell(p) ==
    LET cnt == LiveNeighborsCount(p) IN
    IF A[p] THEN
        (cnt = 2) \/ (cnt = 3)
    ELSE
        cnt = 3

(* --next-state relation: simultaneous update of all cells *)
Next ==
    /\ A' = [p \in Coords |-> UpdateCell(p)]

(* --safety type invariant: A always maps each coordinate to a Boolean value *)
TypeOK == A \in [Coords -> BOOLEAN]

Spec == Init /\ [][Next]_<<A>>

====