---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

VARIABLE grid

(* The set of all positions on the N×N grid *)
Positions == {1 .. N} \X {1 .. N}

(* The eight (or fewer) neighbours of a position, staying inside the grid. *)
Neighbors(p) == { q \in Positions :
                    q # p /\ 
                    Abs(q[1] - p[1]) <= 1 /\ Abs(q[2] - p[2]) <= 1 }

(* Number of live neighbours of p in the given grid mapping g. *)
Count(p, g) == Cardinality({ q \in Neighbors(p) : g[q] })

(* Type invariant: grid maps every position to a Boolean value. *)
TypeOK == grid \in [Positions -> BOOLEAN]

(* Any Boolean assignment to all cells is a possible initial state. *)
Init == /\ TypeOK

(* Simultaneous update according to Conway's rules. *)
Next == 
    /\ grid' = [p \in Positions |-> 
                 IF grid[p] 
                 THEN (Count(p, grid) = 2) \/ (Count(p, grid) = 3)
                 ELSE Count(p, grid) = 3
               ]

(* Full specification: start in Init and repeatedly apply Next. *)
Spec == Init /\ [] [Next]_<<grid>>

====