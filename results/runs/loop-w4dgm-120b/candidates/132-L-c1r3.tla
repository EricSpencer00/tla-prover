---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in UNION { [1..n -> Values] : n \in 0..bound }
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

Spec == Init /\ [][Next]_vars /\ WF_vars(Advance)

Init ==
  /\ seq \in UNION { [1..n -> Values] : n \in 0..bound }
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Advance ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       cand' = IF cnt = 0 THEN x
               ELSE IF x = cand THEN cand
               ELSE cand
  /\ cnt' = IF cnt = 0 THEN 1
            ELSE IF seq[pos] = cand THEN cnt + 1
            ELSE cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Advance

Correct ==
  \A e \in Values : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = e}) > Len(seq))
                      => e = cand

Inv ==
  /\ cnt \in 0..Len(seq)
  /\ (cnt = 0 => pos = 1 \/ (pos > 1 /\ seq[pos - 1] # cand))

BoundedSeq == Seq

Properties == Spec
====