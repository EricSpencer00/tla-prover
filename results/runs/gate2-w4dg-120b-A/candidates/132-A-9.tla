---- MODULE MCMajority ----
EXTENDS Naturals

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

SeqSpace == {s \in Seq : s[1] <= bound}
SeqElem(s, i) == IF s[1] < i THEN Values ELSE s[i]

VARIABLES seq, pos, cand, ctr
vars == <<seq, pos, cand, ctr>>

TypeOK ==
    /\ seq \in SeqSpace
    /\ pos \in 1..(bound + 1)
    /\ cand \in Values
    /\ ctr \in 0..bound

Init ==
    /\ seq \in SeqSpace
    /\ pos = 1
    /\ cand \in Values
    /\ ctr = 0

Next ==
    /\ pos <= bound
    /\ LET x == SeqElem(seq, pos) IN
         /\ IF ctr = 0 THEN /\ cand' = x
                          /\ ctr' = 1
            ELSE IF cand = x THEN ctr' = ctr + 1
            ELSE ctr' = ctr - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Spec == Init /\ [][Next]_vars
    /\ WF_vars(Next)

Correct ==
    \A v \in Values : (Cardinality({i \in 1..seq[1] : seq[i] = v}) > seq[1] \div 2) => (cand = v)

Inv == TypeOK
====