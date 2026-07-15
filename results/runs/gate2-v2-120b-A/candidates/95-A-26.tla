---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N

\* ----------------------------------------------------------------------
\* Types and sets
\* ----------------------------------------------------------------------
CellPos == 1..N \X 1..N           \* All valid positions on the N-by-N grid

\* ----------------------------------------------------------------------
\* State variable
\* ----------------------------------------------------------------------
VARIABLE Grid

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Neighbors(p) == 
  { <<i, j>> : 
      i \in {p[1]-1, p[1], p[1]+1} /\ 
      j \in {p[2]-1, p[2], p[2]+1} /\ 
      (i # p[1] \/ j # p[2]) /\ 
      i \in 1..N /\ j \in 1..N }

LiveNeighborsCount(g, p) ==
  Cardinality({ q \in Neighbors(p) : g[q] = TRUE })

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
  /\ Grid = [p \in CellPos |-> FALSE] \cup 
            [p \in CellPos |-> TRUE] \* nondeterministic assignment
        \* The expression above nondeterministically picks any mapping
        \* from CellPos to BOOLEAN (TRUE or FALSE) which is exactly the
        \* set of all possible initial configurations.

\* ----------------------------------------------------------------------
\* Next-state relation (Tick)
\* ----------------------------------------------------------------------
Tick ==
  /\ Grid' = [p \in CellPos |-> 
        LET cnt == LiveNeighborsCount(Grid, p) IN
        IF Grid[p] = TRUE THEN
             (cnt = 2) \/ (cnt = 3)
        ELSE
             cnt = 3]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Next == Tick

Spec == Init /\ [][Next]_Grid

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK == 
  /\ Grid \in [CellPos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Theorem (optional, but harmless) to expose the invariant to TLC
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====