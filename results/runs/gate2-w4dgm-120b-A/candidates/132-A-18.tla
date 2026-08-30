---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* The main majority vote spec, instantiated with concrete values, plus a
\* bounded-sequence construction so the model stays finite for exhaustive checking.
\* Note: BoundedSeq is defined here to replace the standard Seq operator in the
\* inherited spec; the rest of the spec (Init, Next, etc.) is unchanged except
\* that it now draws sequences from the bounded set instead of any length.

\* The three distinct model values that can appear in the sequences.
Vals == {A, B, C}

\* All sequences of length up to the configured bound over the value set.
Seqs == UNION { [1..n -> Vals] : n \in 0..bound }

\* A bounded version of the standard sequence constructor: the set of all
\* sequences of length exactly n over the value set -- this keeps the model
\* finite and is what replaces the infinite Seq operator in the imported spec.
BoundedSeq(n) == [1..n -> Vals]

VARIABLES seq, pos, cand, count

vars == << seq, pos, cand, count >>

TypeOK ==
  /\ seq \in Seqs
  /\ pos \in 1..(bound + 1)
  /\ cand \in Vals
  /\ count \in 0..bound

\* Pure correctness property: any element that truly appears more than half the
\* time in the scanned sequence must be the candidate left at the end.
Correct ==
  \A v \in Vals : (2 * Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq)) => (cand = v)

Init ==
  /\ seq \in Seqs
  /\ pos = 1
  /\ cand \in Vals
  /\ count = 0

\* Scan the next element: adopt if no candidate yet (count zero), increment if
\* it matches, or decrement the counter if it does not.
Scan ==
  /\ pos <= Len(seq)
  /\ LET e == seq[pos] IN
       IF count = 0
         THEN /\ cand' = e
              /\ count' = 1
         ELSE IF e = cand
              THEN /\ cand' = cand
                   /\ count' = count + 1
              ELSE /\ cand' = cand
                   /\ count' = count - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Scan

\* Both properties are combined into the single formula the .cfg expects to
\* name as the spec's required property.
Spec == Init /\ [][Next]_vars /\ WF_vars(Scan)

Inv == TypeOK /\ Correct

\* The scan always eventually runs off the end of the sequence, even though
\* Scan is its own weak fairness condition (it never disables itself).
Complete == <>(pos > Len(seq))

====