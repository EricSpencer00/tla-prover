---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

\* Grid coordinates
Cells == 1..N
Arr == Cells \X Cells

\* Sum of live neighbors around position p in the current state f
NbrSum(f, p) ==
  LET (r, c) == p IN
    LET neigh == {q \in Arr : q # p /\ (r - q[1]) \in 0..1 /\ (c - q[2]) \in 0..1} IN
      Cardinality({q \in neigh : f[q]})

VARIABLES cell
vars == <<cell>>

TypeOK == cell \in [Arr -> BOOLEAN]

Init ==
  \E c \in [Arr -> BOOLEAN] : cell = c

Tick ==
  /\ \E c \in [Arr -> BOOLEAN] :
       /\ \A p \in Arr :
            LET live == (NbrSum(cell, p) = 3 \/ (cell[p] /\ NbrSum(cell, p) = 2)) IN
              c[p] = live
       /\ cell' = c
  /\ UNCHANGED vars

Next == Tick

Spec == Init /\ [][Next]_vars

====