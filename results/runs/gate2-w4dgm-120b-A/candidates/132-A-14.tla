---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, counter

vars == <<seq, pos, cand, counter>>

Ambiguous == CHOOSE c \in Values : TRUE

TypeOK ==
    /\ seq \in UNION { Values^n : n \in 0..bound }
    /\ pos \in 1..(bound + 1)
    /\ cand \in Values
    /\ counter \in 0..bound

Init ==
    /\ seq \in UNION { Values^n : n \in 0..bound }
    /\ pos = 1
    /\ cand \in Values
    /\ counter = 0

Scan ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
        /\ IF counter = 0 THEN /\ cand' = x /\ counter' = 1
           ELSE IF x = cand THEN /\ cand' = cand /\ counter' = counter + 1
           ELSE /\ cand' = cand /\ counter' = counter - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Spec == Init /\ [][Scan]_vars
    /\ WF_vars(Scan)

Correct ==
    /\ (pos > Len(seq) => counter = 0 \/ cand = seq[1] \/ cand = seq[2])
    /\ (pos > Len(seq) => \A i \in 1..Len(seq) : seq[i] = cand => 2 * Cardinality({j \in 1..Len(seq) : seq[j] = cand}) > Len(seq))

Inv ==
    /\ counter <= Len(seq)
    /\ (pos > 1 /\ counter > 0 => cand = seq[pos - 1])

BoundedSeq == UNION { Values^n : n \in 0..bound }

====