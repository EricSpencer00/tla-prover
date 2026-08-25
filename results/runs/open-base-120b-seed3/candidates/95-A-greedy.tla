---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

VARIABLES grid

(* The set of all positions on the N×N grid *)
Cell == 1..N \X 1..N

(* Type invariant: grid maps every cell to a Boolean value *)
TypeOK == grid \in [Cell -> BOOLEAN]

(* Initial state: any mapping of cells to Booleans is allowed *)
Init == 
    /\ TypeOK

(* Helper: number of live neighbours of a cell p in the current grid *)
Cnt(p) == 
    Cardinality(
        { q \in Cell :
            /\ p # q
            /\ (p[1] - q[1]) \in -1..1
            /\ (p[2] - q[2]) \in -1..1
            /\ grid[q] } )

(* Next-state relation: simultaneous update of all cells *)
Next == 
    /\ grid' = [p \in Cell |-> 
                IF grid[p] 
                THEN (Cnt(p) = 2) \/ (Cnt(p) = 3) 
                ELSE (Cnt(p) = 3)]

(* Full specification *)
Spec == Init /\ [] [Next]_<<grid>>

====