---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT N

VARIABLES A

(* The set of all positions on the N×N grid *)
CellSet == 1..N \X 1..N

(* Two positions are neighbors if they are distinct and at most one step apart in each coordinate *)
IsNeighbor(p, q) ==
  /\ p # q
  /\ Abs(p[1] - q[1]) <= 1
  /\ Abs(p[2] - q[2]) <= 1

(* Number of live neighbours of position p in the current state A *)
LiveNeighbors(p) ==
  Cardinality({ q \in CellSet : IsNeighbor(q, p) /\ A[q] })

(* Type invariant: A is a total mapping from CellSet to BOOLEAN *)
TypeOK == A \in [CellSet -> BOOLEAN]

(* Any assignment of booleans to all cells is allowed initially *)
Init == A \in [CellSet -> BOOLEAN]

(* Simultaneous update of the whole grid *)
Next ==
  LET Anew == 
        [p \in CellSet |-> 
          IF ( A[p] /\ (LiveNeighbors(p) = 2 \/ LiveNeighbors(p) = 3) )
                \/ ( ~A[p] /\ LiveNeighbors(p) = 3 )
          THEN TRUE
          ELSE FALSE ]
  IN  A' = Anew

(* Full specification *)
Spec == Init /\ [][Next]_<<A>>

====