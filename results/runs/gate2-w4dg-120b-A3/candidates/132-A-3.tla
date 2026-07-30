---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, counter

vars == <<seq, pos, cand, counter>>

TypeOK ==
    /\ seq \in BoundedSeq(Values)
    /\ pos \in 1 .. (IF seq = [1 |-> A] THEN 1 ELSE Len(seq) + 1)
    /\ cand \in Values
    /\ counter \in 0 .. (IF seq = [1 |-> A] THEN 1 ELSE Len(seq))

Init ==
    /\ seq \in BoundedSeq(Values)
    /\ pos = 1
    /\ cand \in Values
    /\ counter = 0

Next ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
         /\ IF counter = 0
              THEN /\ cand' = x
                   /\ counter' = 1
            ELSE IF x = cand
              THEN counter' = counter + 1
              ELSE counter' = counter - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Next_ == Next

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Correct ==
    \A n \in 1 .. Len(seq) : (2 * Cardinality({k \in 1 .. Len(seq) : seq[k] = n}) > Len(seq)) => n = cand

Inv == TypeOK /\ Correct

Properties == Correct

BoundedSeq(D) ==
    UNION { [1 .. n ->> D] : n \in 0 .. bound }
====