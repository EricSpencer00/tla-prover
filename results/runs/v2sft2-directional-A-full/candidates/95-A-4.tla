---- MODULE GameOfLife ----
EXTENDS FiniteSets, Integers

CONSTANT N

VARIABLE Alive

(* The set of all grid positions, represented as ordered pairs (row, col). *)
Positions == { <<r, c>> : r \in 1..N, c \in 1..N }

(* The set of neighboring positions of a given position p. *)
Neighbors(p) == { q \in Positions :
                 (Abs(p[1] - q[1]) <= 1) /\ (Abs(p[2] - q[2]) <= 1) /\ (p # q) }

(* Initial state: each cell is nondeterministically alive or dead. *)
Init == Alive \in [p \in Positions -> BOOLEAN]

(* Deterministic simultaneous update according to Conway's rules. *)
Next ==
  \E Alive' \in [p \in Positions -> BOOLEAN] :
    \A p \in Positions :
      LET cnt == Cardinality({ q \in Positions : q \in Neighbors(p) /\ Alive[q] }) IN
        Alive'[p] = (Alive[p] /\ (cnt = 2 \/ cnt = 3)) \/ (~Alive[p] /\ cnt = 3)

(* Specification that combines the initial state and the repeated application of Next. *)
Spec == Init /\ [][Next]_<<Alive>>

(* Type invariant ensuring Alive always maps each position to a boolean. *)
TypeOK == Alive \in [p \in Positions -> BOOLEAN]

====