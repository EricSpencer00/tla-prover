---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES A

(* The set of all positions on the N×N grid *)
Pos == 1..N \X 1..N

(* Type invariant: A maps each position to a Boolean value *)
TypeOK == A \in [Pos -> BOOLEAN]

(* Initial state: any mapping from positions to Booleans is allowed *)
Init == /\ TypeOK

(* Number of live neighbors of position p *)
Count(p) ==
  Cardinality({
    q \in Pos :
      q # p /\                     \* not the same cell
      Abs(q[1] - p[1]) <= 1 /\     \* row distance at most 1
      Abs(q[2] - p[2]) <= 1 /\     \* column distance at most 1
      A[q]                        \* neighbor is alive
  })

(* Simultaneous update of the whole grid *)
Next ==
  /\ A' = [p \in Pos |->
        IF A[p] /\ (Count(p) = 2 \/ Count(p) = 3) THEN TRUE
        ELSE IF ~A[p] /\ Count(p) = 3 THEN TRUE
        ELSE FALSE ]

(* The full specification *)
Spec == Init /\ [][Next]_A
====