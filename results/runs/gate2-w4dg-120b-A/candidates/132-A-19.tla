---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

\* Sequences of bounded length over the three model values are built as the
\* finite set of functions from 1..n to Values, for n ranging from zero up to
\* the configured bound.  This keeps the state space finite for model checking.
Seqs == UNION { [1..n -> Values] : n \in 0..bound }

VARIABLES seq, i, cand, count

vars == <<seq, i, cand, count>>

TypeOK ==
  /\ seq \in Seqs
  /\ i \in Nat
  /\ cand \in Values
  /\ count \in Nat

\* The candidate must be drawn from the value set; count never exceeds the bound.
Inv ==
  /\ cand \in Values
  /\ count <= bound

Init ==
  /\ seq \in Seqs
  /\ i = 1
  /\ cand \in Values
  /\ count = 0

\* Scan the next element with the Boyer-Moore three-case logic: adopt a new
\* candidate if the counter is zero, increment the counter on a match, or
\* decrement it on a mismatch.
Next ==
  \/ /\ i <= Len(seq)
     /\ LET x == seq[i] IN
          /\ cand' = IF count = 0 THEN x ELSE cand
          /\ count' = IF count = 0 THEN 1
                      ELSE IF cand = x THEN count + 1
                      ELSE count - 1
     /\ i' = i + 1
     /\ UNCHANGED seq
  \/ /\ seq' \in Seqs
     /\ UNCHANGED <<i, cand, count>>

Spec == Init /\ [][Next]_vars

\* A true majority found by a complete scan must be the lasting candidate.
Correct ==
  (i > Len(seq) /\ count > 0 /\ 2 * (Cardinality({ k \in 1..Len(seq) : seq[k] = cand })) > Len(seq)) => TRUE

\* Fairness: the scan never stalls forever.
Fairness == WF_vars(Next)

====