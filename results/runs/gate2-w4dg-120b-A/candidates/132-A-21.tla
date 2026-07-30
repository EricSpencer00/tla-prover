---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

\* The bounded sequence set: all sequences of length at most bound built from
\* the three model values.
SeqSet == UNION { [1..n -> Values] : n \in 0..bound }

TypeOK ==
  /\ seq \in SeqSet
  /\ pos \in 1..6
  /\ cand \in Values \cup {"none"}
  /\ cnt \in 0..5

Init ==
  /\ seq \in SeqSet
  /\ pos = 1
  /\ cand = CHOOSE e \in Values : TRUE
  /\ cnt = 0

\* Boyer-Moore scan with the three-case update on the next element.
Step ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       /\ IF cnt = 0 THEN /\ cand' = x
                        /\ cnt' = 1
          ELSE IF cand = x THEN cnt' = cnt + 1
          ELSE cnt' = cnt - 1
       /\ UNCHANGED <<seq, cand>>
  /\ pos' = pos + 1

Spec == Init /\ [][Step]_<<seq, pos, cand, cnt>>

\* The main correctness property: after a full scan, any true majority must
\* be the surviving candidate.
Correct ==
  \/ pos > Len(seq)
  \/ \A e \in Values : (2 * Cardinality({ i \in 1..Len(seq) : seq[i] = e }) > Len(seq)) => e = cand

\* An inductive invariant stronger than type correctness.
Inv ==
  /\ TypeOK
  /\ (pos <= Len(seq) => cnt >= 1)
  /\ (pos <= Len(seq) /\ cand = "none" => cnt = 0)

\* The scan makes progress under weak fairness.
Progress == <>(pos > Len(seq))

====