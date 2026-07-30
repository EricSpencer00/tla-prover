---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* The three model values and the sequence length bound are concrete
\* (no parameters to choose) and the full set of sequences is defined
\* as a bounded, finite collection -- not the standard unbounded Seq.
Values == {A, B, C}

\* Finite version of the standard Seq operator: a concrete set of
\* sequences rather than the infinite comprehension in Sequences.
BoundedSeq == { s \in [1..n -> Values] : n \in 0..bound }

\* The rest of the model is exactly the majority-vote spec; only the
\* sequence domain is swapped in.
VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1..bound
  /\ cand \in Values
  /\ count \in 0..bound

Scan ==
  /\ pos < Len(seq)
  /\ LET x == seq[pos + 1] IN
       IF count = 0
         THEN /\ cand' = x
              /\ count' = 1
         ELSE IF x = cand
              THEN count' = count + 1
              /\ cand' = cand
              /\ UNCHANGED <<seq, pos>>
         ELSE count' = count - 1
              /\ cand' = cand
              /\ UNCHANGED <<seq, pos>>
  /\ pos' = pos + 1

Idle ==
  /\ pos = Len(seq)
  /\ UNCHANGED vars

Reinit ==
  /\ \/ pos = Len(seq)
     \/ (pos > Len(seq) /\ Len(seq) < bound)
  /\ \E s \in BoundedSeq :
       /\ seq' = s
       /\ pos' = 1
       /\ cand' \in Values
       /\ count' = 0

Next == Scan \/ Idle \/ Reinit

Init ==
  /\ \E s \in BoundedSeq :
       /\ seq' = s
       /\ pos' = 1
       /\ cand' \in Values
       /\ count' = 0

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Scan) /\ WF_vars(Reinit)

Correct ==
  \A i \in 1..Len(seq) : (2 * Cardinality({ j \in 1..Len(seq) : seq[j] = seq[i] }) > Len(seq))
                         => seq[i] = cand

Inv ==
  /\ count >= 0
  /\ IF count = 0 THEN cand \in Values
     ELSE \A i \in 1..Len(seq) : seq[i] = cand

====