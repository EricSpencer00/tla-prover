---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

VARIABLE Grid

(*-------------------------------------------------------------------*)
(*  Types and helper definitions                                      *)
(*-------------------------------------------------------------------*)

Pos == [i : 1..N, j : 1..N]

Neighbors(pos) ==
  { p \in Pos :
      (p.i # pos.i \/ p.j # pos.j) /\ 
      Abs(p.i - pos.i) <= 1 /\ Abs(p.j - pos.j) <= 1 }

NeighborCount(pos, g) ==
  Cardinality({ p \in Neighbors(pos) : g[p] })

AliveNext(pos, g) ==
  IF g[pos] THEN
    LET cnt == NeighborCount(pos, g) IN cnt = 2 \/ cnt = 3
  ELSE
    LET cnt == NeighborCount(pos, g) IN cnt = 3

(*-------------------------------------------------------------------*)
(*  Initialization and transition                                    *)
(*-------------------------------------------------------------------*)

Init ==
  /\ Grid \in [Pos -> BOOLEAN]

Tick ==
  /\ Grid' = [pos \in Pos |-> AliveNext(pos, Grid)]

Next ==
  Tick

Spec ==
  Init /\ [][Next]_<<Grid>>

(*-------------------------------------------------------------------*)
(*  Invariant                                                        *)
(*-------------------------------------------------------------------*)

TypeOK ==
  /\ Grid \in [Pos -> BOOLEAN]

====