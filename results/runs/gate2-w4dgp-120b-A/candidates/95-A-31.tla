---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

\* A position in the square grid, and the set of all valid positions.
Pos == {1..N} \X {1..N}

\* The eight directions from a cell to its immediate neighbors (including diagonals).
Dirs == {<<-1, -1>>, <<-1, 0>>, <<-1, 1>>, <<0, -1>>, <<0, 1>>, <<1, -1>>, <<1, 0>>, <<1, 1>>}

VARIABLES cells

vars == <<cells>>

TypeOK ==
    /\ cells \in [Pos -> BOOLEAN]

\* Sum of the values of a small finite set of booleans.  Used for counting
\* neighbors; a dead cell contributes 0, a living cell contributes 1.
boolSum(S) == LET f[T \in SUBSET S] ==
                    IF T = {} THEN 0
                    ELSE LET x == CHOOSE y \in T : TRUE
                         IN (IF cells[x] THEN 1 ELSE 0) + f[T \ {x}]
               IN f[S]

Neighbors(p) == {<<p[1] + d[1], p[2] + d[2]>> : d \in Dirs}

\* The neighbor count treats any position outside the grid as dead (0),
\* because those positions never appear in Pos and therefore never
\* contribute to boolSum.
Live(p) == boolSum(Neighbors(p) \cap Pos)

Init ==
    /\ cells \in [Pos -> BOOLEAN]

\* Simultaneous deterministic update of every cell based on its live neighbor count.
Tick ==
    /\ cells' =
        [p \in Pos |->
            \/ /\ cells[p] = TRUE
               /\ Live(p) \in {2, 3}
               /\ TRUE
            \/ /\ cells[p] = FALSE
               /\ Live(p) = 3
               /\ TRUE
            \/ ~((cells[p] = TRUE /\ Live(p) \in {2, 3}) \/ (cells[p] = FALSE /\ Live(p) = 3))
               /\ FALSE]
    /\ UNCHANGED << >>

Next == Tick

Spec == Init /\ [][Next]_vars

====