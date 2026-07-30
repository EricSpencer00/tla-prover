---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

\* Concrete values for the Boyer-Moore majority vote specification.
CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

\* Sequences of length at most 'bound' over Values, constructed as functions
\* from 1..n for some n <= bound, collected into a set.
AllSeqs == UNION { [1..n -> Values] : n \in 0..bound }

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

TypeOK ==
  /\ seq \in AllSeqs
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ count \in 0..bound

Init ==
  /\ seq \in AllSeqs
  /\ pos = 1
  /\ cand \in Values
  /\ count = 0

\* The three-case logic of Boyer-Moore: adopt a candidate, increment, or decrement.
NextStep ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF count = 0
         THEN /\ cand' = x
              /\ count' = 1
         ELSE IF cand = x
              THEN /\ count' = count + 1
              /\ UNCHANGED <<cand>>
              ELSE /\ count' = count - 1
                   /\ UNCHANGED <<cand>>
  /\ pos' = pos + 1
  /\ UNCHANGED <<seq>>

Next == NextStep

Spec == Init /\ [][Next]_vars /\ WF_vars(NextStep)

\* Any true majority element must equal the candidate after a complete scan.
Correct ==
  \A e \in Values : (2 * Cardinality({ i \in 1..Len(seq) : seq[i] = e }) > Len(seq))
                       => e = cand

\* A simple type invariant that also bounds the candidate counter.
Inv ==
  /\ cand \in Values
  /\ count \in 0..bound
  /\ pos \in 1..(bound + 1)

====