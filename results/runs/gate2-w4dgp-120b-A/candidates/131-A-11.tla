---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, MainMajority

CONSTANTS Value

VARIABLES seq, pos, cand, cnt, done

vars == <<seq, pos, cand, cnt, done>>

TypeOK ==
    /\ seq \in (Value -> {1, 2, 3})
    /\ pos \in 0..3
    /\ cand \in Value
    /\ cnt \in 0..3
    /\ done \in BOOLEAN

Inv ==
    /\ pos \in 0..3
    /\ cand \in Value
    /\ cnt \in 0..3

Init ==
    /\ seq = [i \in {1, 2, 3} |-> CHOOSE v \in Value : TRUE]
    /\ pos = 0
    /\ cand = CHOOSE v \in Value : TRUE
    /\ cnt = 0
    /\ done = FALSE

Vote ==
    /\ ~done
    /\ pos < 3
    /\ LET x == seq[pos + 1] IN
        IF cnt = 0 THEN /\ cand' = x /\ cnt' = 1
        ELSE IF cand = x THEN /\ cand' = cand /\ cnt' = cnt + 1
        ELSE /\ cand' = cand /\ cnt' = cnt - 1
    /\ pos' = pos + 1
    /\ UNCHANGED <<seq, done>>

Verify ==
    /\ ~done
    /\ pos = 3
    /\ done' = TRUE
    /\ UNCHANGED <<seq, pos, cand, cnt>>

Spec == Init /\ [][Vote]_vars /\ [][Verify]_vars

TypeOKInv == Init /\ [][TypeOK]_vars

Correct ==
    /\ done
    /\ \A v \in Value : (3 < 2 * Cardinality({i \in {1, 2, 3} : seq[i] = v}) => v = cand)

SpecOK == Spec /\ Inv

====