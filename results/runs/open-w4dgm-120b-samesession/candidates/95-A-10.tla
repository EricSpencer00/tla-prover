---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Cells == {1 .. N} \X {1 .. N}

VARIABLES alive

vars == <<alive>>

TypeOK ==
  /\ alive \in [Cells -> BOOLEAN]

\* The number of live cells adjacent to a given cell (orthogonal and diagonal),
\* counting cells outside the grid as dead.
Neighbors(r, c) ==
  Cardinality({p \in Cells : \E dr \in -1 .. 1, dc \in -1 .. 1 :
                    p = <<r + dr, c + dc>> /\ ~(dr = 0 /\ dc = 0)
                                                /\ r + dr >= 1
                                                /\ r + dr <= N
                                                /\ c + dc >= 1
                                                /\ c + dc <= N
                                                /\ alive[<<r + dr, c + dc>>]})

Init ==
  \E a \in [Cells -> BOOLEAN] : alive = a

Tick ==
  /\ alive' = [p \in Cells |-> LET n == Neighbors(p[1], p[2]) IN
                     IF alive[p] /\ (n = 2 \/ n = 3) THEN TRUE
                     ELSE IF ~alive[p] /\ n = 3 THEN TRUE
                     ELSE FALSE]

Spec ==
  /\ Init
  /\ [][Tick]_vars

====