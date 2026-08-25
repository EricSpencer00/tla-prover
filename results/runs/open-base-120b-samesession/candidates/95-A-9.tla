---- MODULE GameOfLife ----
EXTENDS FiniteSets, Naturals

CONSTANT N

VARIABLES Grid

(*---------------------------------------------------------------*)
(*   The set of positions on the N-by-N grid                       *)
(*---------------------------------------------------------------*)
Pos == 1..N \X 1..N

(*---------------------------------------------------------------*)
(*   Neighbor relation: the eight surrounding cells (if any)      *)
(*---------------------------------------------------------------*)
Neighbors(p) ==
  { q \in Pos :
      LET i1 == p[1] , j1 == p[2] ,
          i2 == q[1] , j2 == q[2] IN
        (i2 # i1 \/ j2 # j1)                      \* not the cell itself
        /\ i2 >= i1 - 1 /\ i2 <= i1 + 1
        /\ j2 >= j1 - 1 /\ j2 <= j1 + 1 }

(*---------------------------------------------------------------*)
(*   Number of live neighbours of a position                       *)
(*---------------------------------------------------------------*)
CountLive(p) ==
  Cardinality({ q \in Pos : q \in Neighbors(p) /\ Grid[q] })

(*---------------------------------------------------------------*)
(*   Type invariant: Grid maps each position to a Boolean value   *)
(*---------------------------------------------------------------*)
TypeOK == Grid \in [Pos -> BOOLEAN]

(*---------------------------------------------------------------*)
(*   Initial state: any Boolean assignment to the grid             *)
(*---------------------------------------------------------------*)
Init == Grid \in [Pos -> BOOLEAN]

(*---------------------------------------------------------------*)
(*   One synchronous tick: all cells update simultaneously       *)
(*---------------------------------------------------------------*)
Next ==
  /\ \A p \in Pos :
        LET cnt == CountLive(p) IN
          Grid'[p] = IF Grid[p] THEN (cnt = 2 \/ cnt = 3) ELSE (cnt = 3)
  /\ UNCHANGED << >>

(*---------------------------------------------------------------*)
(*   Full specification                                            *)
(*---------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<Grid>>

=============================================================================