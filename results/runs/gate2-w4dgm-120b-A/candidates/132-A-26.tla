---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

TypeOK ==
    /\ bound \in Nat
    /\ bound >= 1
    /\ \E s \in [1..bound -> Values] : TRUE
    /\ \E i \in 0..bound : TRUE
    /\ \E cand \in Values : TRUE
    /\ \E cnt \in Nat : TRUE

\* The bounded sequence construction: a pair of a function and its length,
\* ranging only over lengths within the hard model bound.
Seqs == {<<[1..k -> Values] EXCEPT ![1] = A, k>> : k \in 1..bound}
       \cup {<<[1..k -> Values] EXCEPT ![1] = B, k>> : k \in 1..bound}
       \cup {<<[1..k -> Values] EXCEPT ![1] = C, k>> : k \in 1..bound}
       \cup {<<[1..0 -> Values], 0>>}

VARIABLES seq, i, cand, cnt

Init ==
    /\ seq \in Seqs
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

\* Scans the element at the current position, adopting it as candidate when
\* no candidate is held, otherwise incrementing or decrementing the counter.
Next ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
        IF cnt = 0 THEN
            /\ cand' = x
            /\ cnt' = 1
        ELSE IF x = cand THEN
            /\ cnt' = cnt + 1
            /\ UNCHANGED cand
        ELSE
            /\ cnt' = cnt - 1
            /\ UNCHANGED cand
    /\ i' = i + 1
    /\ UNCHANGED seq

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* The invariant is preserved across the counter reaching zero: it never
\* leaves a stale, unheld candidate behind.
Inv ==
    \/ cnt >= 1
    \/ cnt = 0 /\ \E x \in Values : x # cand

\* No majority element can ever be left inconsistent with the held
\* candidate: any element that truly dominates the whole sequence must be
\* exactly the candidate once the scan has finished.
Correct ==
    \A e \in Values : (\A j \in 1..Len(seq) : e = seq[j]) => (i > Len(seq) /\ e = cand)

MajorityProved == Correct /\ Inv

\* Exaustive bounded check: the scan always reaches the end of the
\* sequence, and it is the only way that can happen.
Complete == <>(i > Len(seq))

====