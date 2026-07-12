---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES G

(* ----------------------------------------------------------------------
   Types and helper definitions
   ---------------------------------------------------------------------- *)

Positions == { [r \in 0..(N-1), c \in 0..(N-1)] |

    }  \* Set of all valid positions in the N-by-N grid

(* Neighbour positions (including diagonals) for a given position *)
Neighbour(pos) == 
    { [r' \in pos.r-1 .. pos.r+1, c' \in pos.c-1 .. pos.c+1] | 
      [r', c'] \in Positions /\ [r', c'] # pos }

(* Count live neighbours of a given position, treating out-of-bounds as dead *)
LiveNeighbourCount(pos) == 
    Cardinality({ n \in Neighbour(pos) | G[n] = TRUE })

(* ----------------------------------------------------------------------
   Init: every cell is nondeterministically alive or dead
   ---------------------------------------------------------------------- *)
Init ==
    /\ G \in [Positions -> BOOLEAN]

(* ----------------------------------------------------------------------
   Next: simultaneous update according to Game of Life rules
   ---------------------------------------------------------------------- *)
Next ==
    /\ G' \in [Positions -> BOOLEAN]
    /\ \A pos \in Positions:
        IF G[pos] = TRUE
          THEN G'[pos] = (LiveNeighbourCount(pos) = 2 \/ LiveNeighbourCount(pos) = 3)
          ELSE G'[pos] = (LiveNeighbourCount(pos) = 3)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<G>>

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK == G \in [Positions -> BOOLEAN]

=============================================================================