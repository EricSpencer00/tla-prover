---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, i, candidate, counter

vars == <<seq, i, candidate, counter>>

\* BoundedSeq replaces the standard infinite Seq with a finite one so the
\* model stays checkable; it is still defined in terms of Sequences (via the
\* function representation).
BoundedSeq == UNION { [1..n -> Values] : n \in 0..bound }

TypeOK ==
  /\ seq \in BoundedSeq
  /\ i \in 0..bound
  /\ candidate \in Values
  /\ counter \in 0..bound

Init ==
  /\ seq \in BoundedSeq
  /\ i = 1
  /\ candidate \in Values
  /\ counter = 0

\* The Boyer-Moore scan: adopt a candidate when none is held, reinforce it
\* when the next element agrees, or demote it when it does not.
Next ==
  \/ /\ i <= bound
     /\ i' = i + 1
     /\ \E e \in Values :
          /\ seq' = [seq EXCEPT ![i] = e]
          /\ IF counter = 0
               THEN /\ candidate' = e
                    /\ counter' = 1
               ELSE IF candidate = e
                    THEN /\ candidate' = candidate
                         /\ counter' = counter + 1
                    ELSE /\ candidate' = candidate
                         /\ counter' = counter - 1
  \/ /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(Next)

\* The main invariant: a true majority must be the candidate after a full
\* scan. The count is taken over the finite prefix of seq examined so far.
Correct ==
  \A e \in Values :
    ( Cardinality({j \in 1..bound : j <= i /\ seq[j] = e}) * 2 > bound )
      => e = candidate

Inv ==
  /\ TypeOK
  /\ Correct

====