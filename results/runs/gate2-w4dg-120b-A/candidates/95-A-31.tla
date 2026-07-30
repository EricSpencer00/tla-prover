---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

ASSUME N \in Nat /\ N > 0

\* Ordered pairs of row and column indices that name the positions of the
\* bounded grid.  Positions outside this set are treated as dead when counting.
Positions == 1..N \X 1..N

Neighbors == UNION {[x \in Positions |-> {p \in Positions :
                    p # x /\ p[1] >= x[1] - 1 /\ p[1] <= x[1] + 1
                         /\ p[2] >= x[2] - 1 /\ p[2] <= x[2] + 1}]}

VARIABLES alive

vars == <<alive>>

OnCount(x) == Cardinality({p \in Neighbors[x] : alive[p]})

Init ==
  /\ alive \in [Positions -> BOOLEAN]

\* Fully deterministic simultaneous update: the next state of every cell is
\* computed from the current state, with no nondeterministic choice.
Tick ==
  /\ alive' = [x \in Positions |->
                  \/ /\ alive[x] /\ (OnCount(x) = 2 \/ OnCount(x) = 3)
                     /\ TRUE
                     \/ ~alive[x] /\ (OnCount(x) = 3)
                     \/ (OnCount(x) # 2 /\ OnCount(x) # 3)
                     /\ FALSE]
  /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK == alive \in [Positions -> BOOLEAN]

====