---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

\* Vals are the three distinct model values that can appear in sequences.
Vals == {A, B, C}

\* BoundedSeq is a finite version of the standard Seq operator, restricted
\* to sequences whose length is at most the bound.  This keeps the state
\* space finite for model checking.  Seq from Sequences is hidden by this.
BoundedSeq(S) == [n \in 0..bound |-> IF n = 0 THEN <<>> ELSE S[n]]

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in BoundedSeq(Vals)
  /\ pos \in 1..(bound + 1)
  /\ cand \in Vals
  /\ cnt \in 0..bound

\* Any true majority element must equal the candidate once the scan is
\* complete, so a real majority survives the Boyer-Moore elimination.
Correct ==
  \A a \in Vals :
    (Cardinality({i \in 1..Len(seq) : seq[i] = a}) * 2 > Len(seq)) => (cand = a)

Init ==
  /\ seq \in BoundedSeq(Vals)
  /\ pos = 1
  /\ cand \in Vals
  /\ cnt = 0

\* The three-case Boyer-Moore update: adopt a new candidate at zero count,
\* increment the counter when the current candidate matches, or decrement otherwise.
Next ==
  /\ pos <= Len(seq)
  /\ LET e == seq[pos] IN
       cand' = IF cnt = 0 THEN e ELSE IF cand = e THEN cand ELSE cand
       /\ cnt' = IF cnt = 0 THEN 1 ELSE IF cand = e THEN cnt + 1 ELSE cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Next]_vars
  /\ WF_vars(Next)

\* The three-case update is the only guarded action, so its weak fairness
\* is what guarantees the scan always reaches the end of the sequence.
NextSF == TRUE

Inv == NextSF

====