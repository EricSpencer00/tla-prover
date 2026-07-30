---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Cells == [x : 1 .. N, y : 1 .. N]
Neighbors == {[dx |-> 0, dy |-> 1], [dx |-> 1, dy |-> 0], [dx |-> 0, dy |-> -1],
              [dx |-> -1, dy |-> 0], [dx |-> 1, dy |-> 1], [dx |-> 1, dy |-> -1],
              [dx |-> -1, dy |-> 1], [dx |-> -1, dy |-> -1]}

SumAlive(f, c) ==
  LET add(a, S) ==
       IF S = {} THEN a
       ELSE LET x == CHOOSE y \in S : TRUE
            IN add(a + (IF f[x] THEN 1 ELSE 0), S \ {x})
  IN add(0, {n \in Cells : n.dx = c.x \land n.dy = c.y})

NextA(c, a) == IF a = 3 THEN TRUE ELSE IF a = 2 THEN c ELSE FALSE

VARIABLES alive

vars == <<alive>>

TypeOK == alive \in [Cells -> BOOLEAN]

Init ==
  \E f \in [Cells -> BOOLEAN] : alive = f

Tick ==
  \E f \in [Cells -> BOOLEAN] :
    /\ \A n \in Cells : alive' = [alive EXCEPT ![n] = NextA(alive[n],
                                 SumAlive([m \in Cells |-> alive[m] * ([dx |-> m.x - n.x, dy |-> m.y - n.y] \in Neighbors)], n))]
    /\ \A n \in Cells : f[n] = alive[n]

Next == Tick

Spec == Init /\ [][Next]_vars

====