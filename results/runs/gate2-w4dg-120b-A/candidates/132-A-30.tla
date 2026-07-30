---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

Sequences == UNION {[1 .. n -> Values] : n \in {0 .. bound}}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
    /\ seq \in Sequences
    /\ pos \in 1 .. (Len(seq) + 1)
    /\ cand \in Values
    /\ cnt \in Nat

\* The main correctness property of Boyer-Moore: after a complete scan the
\* candidate (if any) is the unique true majority of the sequence.
Correct ==
    (pos = Len(seq) + 1 /\ cnt > 0) => (\A i \in 1 .. Len(seq) : seq[i] = cand)

Init ==
    /\ seq \in Sequences
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

\* The three-case scan: adopt a new candidate, increment, or decrement.
Next ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
        IF cnt = 0 THEN /\ cand' = x
                         /\ cnt' = 1
        ELSE IF x = cand THEN cnt' = cnt + 1
        ELSE cnt' = cnt - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Inv ==
    /\ cnt >= 0
    /\ \A i \in 1 .. Len(seq) : (cnt = 0 /\ Cand = seq[i]) => cnt > 0
    /\ cand \in Values

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====