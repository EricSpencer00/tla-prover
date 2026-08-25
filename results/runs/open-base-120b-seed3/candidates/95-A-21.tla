---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLE A

(* The set of all positions on the N-by-N grid *)
Pos == 1..N \X 1..N

(* Relative offsets to the eight neighboring cells *)
NeighborOffsets == { <<dx, dy>> :
                      dx \in -1..1,
                      dy \in -1..1,
                      ~(dx = 0 /\ dy = 0) }

(* The neighboring positions of a given cell p (within the grid) *)
Neighbors(p) == {
                  <<p[1] + dx, p[2] + dy>> :
                    <<dx, dy>> \in NeighborOffsets,
                    p[1] + dx \in 1..N,
                    p[2] + dy \in 1..N
                }

(* Number of live neighbors of cell p in the current state *)
NeighborCount(p) == Cardinality({ q \in Neighbors(p) : A[q] })

(* Initial state: any assignment of true/false to every cell *)
Init == A \in [Pos -> BOOLEAN]

(* Simultaneous update of all cells according to Game of Life rules *)
Next == /\ \A p \in Pos:
           LET cnt == NeighborCount(p) IN
               A'[p] = (cnt = 3) \/ (A[p] /\ cnt = 2)

(* Type invariant: A is always a mapping from positions to booleans *)
TypeOK == A \in [Pos -> BOOLEAN]

(* The overall specification *)
Spec == Init /\ [] [Next]_<<A>>

====