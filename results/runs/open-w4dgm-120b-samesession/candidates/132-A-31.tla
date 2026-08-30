---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

BoundedSeq(V, n) == { f \in [1..n -> V] }

TypeOK ==
  /\ seq \in BoundedSeq(Values, bound)
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

Majority == \E x \in Values : 2 * Cardinality({ i \in 1..Len(seq) : seq[i] = x }) > Len(seq)

Inv == \A i \in 1..(pos - 1) : seq[i] = cand

Init ==
  /\ seq \in BoundedSeq(Values, bound)
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Next ==
  \/ \E v \in Values :
       /\ pos <= Len(seq)
       /\ IF seq[pos] = cand THEN cnt' = cnt + 1
          ELSE IF cnt = 0 THEN /\ cand' = v
                          /\ cnt' = 1
          ELSE cnt' = cnt - 1
       /\ pos' = pos + 1
       /\ seq' = seq
  \/ UNCHANGED <<seq, pos, cand, cnt>>

Spec == Init /\ [][Next]_vars /\ \A a \in vars : WF_vars(a)

Correct == Majority => (pos = Len(seq) + 1 /\ cand = seq[1])
====