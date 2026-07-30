---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

SeqBounded(k) == UNION { [1 .. n -> Values] : n \in 0 .. k }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in SeqBounded(bound)
  /\ pos \in Nat
  /\ cand \in Values \cup {0}
  /\ cnt \in 0 .. bound

Init ==
  /\ seq \in SeqBounded(bound)
  /\ pos = 1
  /\ cand \in Values \cup {0}
  /\ cnt = 0

Step ==
  \/ /\ pos <= Len(seq)
     /\ LET x == seq[pos] IN
          /\ cand' = IF cnt = 0 THEN x
                     ELSE IF x = cand THEN cand
                     ELSE cand
          /\ cnt' = IF cnt = 0 THEN 1
                    ELSE IF x = cand THEN cnt + 1
                    ELSE cnt - 1
     /\ pos' = pos + 1
  \/ /\ pos > Len(seq)
     /\ UNCHANGED <<seq, pos, cand, cnt>>

Spec ==
  /\ Init
  /\ [][Step]_vars
  /\ WF_vars(Step)

\* The true majority (strictly more than half the sequence) must be the current
\* candidate once the scan is complete.
Correct ==
  \A x \in Values :
    (2 * Cardinality({ i \in 1 .. Len(seq) : seq[i] = x }) > Len(seq)) =>
      (pos > Len(seq) /\ cand = x)

Inv == TypeOK /\ Correct

====