---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

VARIABLE A

(* The set of all positions on the N-by-N grid *)
Pos == 1..N \X 1..N

(* The eight neighboring positions of p that lie inside the grid *)
Neighbors(p) ==
  { q \in Pos :
      (q[1] \in (p[1] - 1) .. (p[1] + 1)) /\ 
      (q[2] \in (p[2] - 1) .. (p[2] + 1)) /\ q # p }

(* Number of live neighbours of p in the current state *)
NeighborCount(p) ==
  Cardinality({ q \in Neighbors(p) : A[q] })

(* State invariant: A maps every position to a Boolean *)
TypeOK == A \in [Pos -> BOOLEAN]

(* Any Boolean assignment to all cells is allowed initially *)
Init ==
  /\ A \in [Pos -> BOOLEAN]

(* Simultaneous update of all cells according to the Game of Life rules *)
Next ==
  /\ A' = [p \in Pos |
        LET cnt == NeighborCount(p) IN
        IF (A[p] /\ (cnt = 2 \/ cnt = 3)) \/ (~A[p] /\ cnt = 3)
        THEN TRUE
        ELSE FALSE]

(* Full specification *)
Spec == Init /\ [][Next]_A

====