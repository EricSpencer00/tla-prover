---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

(* ------------------------------------------------------------------------- *)
(* State variable: mapping each position (i,j) to a Boolean (TRUE = alive)   *)
(* ------------------------------------------------------------------------- *)
VARIABLE cells

(* ------------------------------------------------------------------------- *)
(* Helper definitions                                                       *)
(* ------------------------------------------------------------------------- *)
RowSet == 1..N
ColSet == 1..N
Positions == RowSet \X ColSet

Neighbors(p) ==
  LET i == p[1] IN
  LET j == p[2] IN
  { <<i + di, j + dj>> :
      di \in {-1,0,1} /\ dj \in {-1,0,1} /\
      (di # 0 \/ dj # 0) /\ 
      i + di \in RowSet /\ j + dj \in ColSet }

LiveNeighborCount(p) ==
  Cardinality({ q \in Neighbors(p) : cells[q] })

(* ------------------------------------------------------------------------- *)
(* Initial predicate: any assignment of TRUE/FALSE to each cell               *)
(* ------------------------------------------------------------------------- *)
Init ==
  /\ cells \in [Positions -> BOOLEAN]
  /\ \A p \in Positions : cells[p] \in {TRUE, FALSE}

(* ------------------------------------------------------------------------- *)
(* Tick action: simultaneous update of all cells                            *)
(* ------------------------------------------------------------------------- *)
Tick ==
  /\ cells' = [p \in Positions |-> 
        IF cells[p] 
           THEN cells[p] /\ (LiveNeighborCount(p) \in {2,3})
           ELSE (LiveNeighborCount(p) = 3)]
  /\ UNCHANGED << >>

Next == Tick

(* ------------------------------------------------------------------------- *)
(* Specification                                                            *)
(* ------------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<cells>>

(* ------------------------------------------------------------------------- *)
(* Safety invariant: type correctness                                       *)
(* ------------------------------------------------------------------------- *)
TypeOK == cells \in [Positions -> BOOLEAN]

====