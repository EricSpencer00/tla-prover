---- MODULE MCMajority ----
EXTENDS Naturals

\* Model values: three distinct elements for the Boyer-Moore algorithm.
CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

NONE == 0

VARIABLES seq, pos, candidate, count

vars == <<seq, pos, candidate, count>>

TypeOK ==
  /\ seq \in Seq
  /\ pos \in 1..(bound + 1)
  /\ candidate \in Values \cup {NONE}
  /\ count \in 0..bound

\* The scanning invariant: either a majority is impossible, or the candidate is
\* the unique majority element.
Inv ==
  \/ \A m \in Values : (2 * Cardinality({k \in DOMAIN seq : seq[k] = m}) <= Cardinality(DOMAIN seq))
  \/ \A m \in Values : (2 * Cardinality({k \in DOMAIN seq : seq[k] = m}) > Cardinality(DOMAIN seq) => candidate = m)

Init ==
  /\ seq \in Seq
  /\ pos = 1
  /\ candidate \in Values \cup {NONE}
  /\ count = 0

\* Boyer-Moore's three-way update: adopt a new candidate, increment the counter,
\* or decrement the counter, each conditioned by the current state.
Next ==
  \/ /\ pos <= bound
     /\ LET x == seq[pos] IN
        \/ /\ candidate = NONE /\ count = 0
           /\ candidate' = x /\ count' = 1
        \/ /\ candidate = x
           /\ count' = count + 1
           /\ UNCHANGED candidate
        \/ /\ candidate # NONE /\ candidate # x /\ count > 0
           /\ count' = count - 1
           /\ UNCHANGED candidate
     /\ pos' = pos + 1
     /\ UNCHANGED seq
  \/ /\ pos > bound
     /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Correct == Inv

====