---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Neighbors == {d \in {0, 1} \X {0, 1} \X {0, 1} : d # <<0, 0, 0>>}

VARIABLES cell

vars == <<cell>>

TypeOK ==
    /\ cell \in [1 .. N \X 1 .. N -> BOOLEAN]

CountAlive(r, c) ==
    Cardinality(
        {d \in Neighbors :
            LET rr == r + d[1] - d[2]
                cc == c + d[3] - d[2]
            IN 1 <= rr /\ rr <= N /\ 1 <= cc /\ cc <= N /\ cell[rr, cc]
        })

NextState(r, c) ==
    IF cell[r, c]
        THEN IF CountAlive(r, c) = 2 \/ CountAlive(r, c) = 3 THEN TRUE ELSE FALSE
        ELSE IF CountAlive(r, c) = 3 THEN TRUE ELSE FALSE

Init ==
    /\ cell \in [1 .. N \X 1 .. N -> BOOLEAN]

Tick ==
    /\ cell' = [p \in 1 .. N \X 1 .. N |-> NextState(p[1], p[2])]

Next == Tick

Spec == Init /\ [][Next]_vars

====