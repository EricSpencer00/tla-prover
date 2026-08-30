---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

\* A finite (bounded) version of the standard Seq constructor: it builds
\* functions from 1..n into the value set, for n up to a fixed bound.
Seqs == { f \in [1..bound -> {A, B, C}] : \E n \in 0..bound : \A i \in 1..bound : i <= n => f[i] # "none" }

VARIABLES seq, pos, cand, ctr

TypeOK ==
  /\ seq \in Seqs
  /\ pos \in 0..bound
  /\ cand \in {A, B, C}
  /\ ctr \in 0..bound

\* A majority that truly exists must be the surviving candidate after a full
\* scan: only the element equal to the candidate can appear in more than half
\* of the positions of a completely scanned sequence.
Correct ==
  \A e \in {A, B, C} : (\A S \in Seq(1..bound) : Cardinality({ i \in 1..BoundSeq(S) : S[i] = e }) * 2 > Cardinality(1..BoundSeq(S)))
                        => (cand = e)

Inv == pos <= bound

Init ==
  /\ seq \in Seqs
  /\ pos = 1
  /\ cand \in {A, B, C}
  /\ ctr = 0

\* The Boyer-Moore update: adopt a new candidate, or adjust the counter up or
\* down as the element matches or mismatches the current candidate.
Next ==
  /\ pos <= bound
  /\ LET x == seq[pos] IN
       IF pos = 1 THEN
         /\ cand' = x
         /\ ctr' = 1
       ELSE IF x = cand THEN
         /\ cand' = cand
         /\ ctr' = ctr + 1
       ELSE
         /\ cand' = cand
         /\ ctr' = ctr - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Next]_<<seq, pos, cand, ctr>>

\* Liveness: once scanning has started it always eventually finishes.
EventuallyComplete == (pos > 1) ~> (pos > bound)

====