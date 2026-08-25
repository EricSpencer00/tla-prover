---- MODULE GameOfLife ----
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE A

(* The set of all positions on the N×N grid *)
Pos == 1..N \X 1..N

(* Two positions are neighbors if they differ by at most 1 in each coordinate
   and are not the same position. Positions outside the grid are simply not
   included in Pos, thus they contribute 0 to the neighbor count. *)
IsNeighbor(p, q) ==
  LET dr == p[1] - q[1] IN
  LET dc == p[2] - q[2] IN
    dr \in -1..1 /\ dc \in -1..1 /\ ~(dr = 0 /\ dc = 0)

(* Number of live neighbours of position p in the current state *)
NeighborCount(p) ==
  Cardinality({ q \in Pos : IsNeighbor(p, q) /\ A[q] })

(* Any assignment of true/false to every cell is a possible initial state *)
Init ==
  A \in [Pos -> BOOLEAN]

(* Simultaneous update of all cells according to Conway's rules *)
Next ==
  LET nc == [p \in Pos |-> NeighborCount(p)] IN
    A' = [p \in Pos |->
            IF A[p] /\ (nc[p] = 2 \/ nc[p] = 3) THEN TRUE
            ELSE IF ~A[p] /\ nc[p] = 3          THEN TRUE
            ELSE FALSE]

(* The full specification *)
Spec == Init /\ [][Next]_A

(* Type invariant: A always maps each position to a Boolean *)
TypeOK == A \in [Pos -> BOOLEAN]

====