---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Neighbors == {[-1 .. 1, -1 .. 1]}

TypeOK == grid \in [1 .. N \X 1 .. N -> BOOLEAN]

Init == grid \in [1 .. N \X 1 .. N -> BOOLEAN]

SumBits(f) ==
  LET Add(r, c, k) == IF r > N THEN k ELSE
                        IF c > N THEN Add(r + 1, 1, k)
                        ELSE Add(r, c + 1, k + (IF f[r, c] THEN 1 ELSE 0))
  IN Add(1, 1, 0)

LiveNeighbors(g, r, c) ==
  LET Count(S, k) == IF S = {} THEN k
                      ELSE LET d == CHOOSE x \in S : TRUE
                           IN Count(S \ {d}, k + (IF (r + d[1] \in 1 .. N /\ c + d[2] \in 1 .. N)
                                                    /\ g[r + d[1], c + d[2]]
                                                    THEN 1 ELSE 0))
  IN Count(Neighbors \ {<<0, 0>>}, 0)

NextGen(g) ==
  [r \in 1 .. N, c \in 1 .. N |-> IF g[r, c]
                                    THEN LiveNeighbors(g, r, c) \in {2, 3}
                                    ELSE LiveNeighbors(g, r, c) = 3]

Tick == grid' = NextGen(grid)

Next == Tick

Spec == Init /\ [][Next]_vars

====