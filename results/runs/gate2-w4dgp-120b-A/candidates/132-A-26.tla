---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound
Values == {A, B, C}

VARIABLES seq, pos, cand, counter
vars == <<seq, pos, cand, counter>>

BoundedSeq(S) == {s \in Seq(S) : Len(s) <= bound}

InitSeq == CHOOSE s \in BoundedSeq(Values) : Len(s) = bound

TypeOK ==
  /\ seq \in BoundedSeq(Values)
  /\ pos \in Nat
  /\ cand \in Values
  /\ counter \in Nat

Init ==
  /\ seq = InitSeq
  /\ pos = 1
  /\ cand \in Values
  /\ counter = 0

\* The majority-vote scan: three cases depending on the counter and whether
\* the current element matches the candidate.
Step ==
  /\ pos <= Len(seq)
  /\ IF counter = 0 THEN
       /\ cand' = seq[pos]
       /\ counter' = 1
     ELSE IF seq[pos] = cand THEN
       /\ counter' = counter + 1
     ELSE
       /\ counter' = counter - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Step]_vars /\ WF_vars(Step)

Correct ==
  \A x \in Values : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq)) => (cand = x)

Inv ==
  \A i \in 1..Len(seq) :
    (counter > 0 /\ i <= pos) => (cand = seq[i])

SpecComplete == Spec /\ <>(pos > Len(seq))

ASSUME bound \in Nat

====