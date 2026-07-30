---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS A, B, C, bound

\* A concrete set of three model values; the bound below is the maximum
\* sequence length the model checker will explore.
Values == {A, B, C}

\* Sequences drawn from a bounded range of lengths, 0..bound, using a
\* finite version of the standard Seq operator (Seq is replaced in the
\* .cfg, so we must leave it undefined here).
BoundedSeq == \E n \in 0..bound : [1..n -> Values]
AllSeqs   == [1..bound -> Values]

VARIABLES seq, i, cand, cnt

vars == << seq, i, cand, cnt >>

TypeOK ==
  /\ seq \in AllSeqs
  /\ i \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

\* The candidate can start as any value; the counter starts at zero, and the
\* scan starts at the first position.
Init ==
  /\ seq \in BoundedSeq
  /\ i = 1
  /\ cand \in Values
  /\ cnt = 0

\* Boyer-Moore scan: a new candidate, a confirmation, or a cancellation.
Next ==
  /\ i <= bound
  /\ \/ /\ cand' = seq[i]
        /\ cnt' = 1
        /\ i' = i + 1
     \/ /\ cnt' = IF cnt = 0
                  THEN 1
                  ELSE IF cand = seq[i]
                          THEN cnt + 1
                          ELSE cnt - 1
        /\ i' = i + 1
        /\ UNCHANGED cand
  /\ UNCHANGED seq

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* The candidate at the end of a full scan must be the unique majority.
Correct ==
  \A x \in Values :
    (2 * Cardinality({i \in 1..bound : seq[i] = x}) > bound) => (cand = x)

\* The inductive invariant from the main spec.
Inv ==
  /\ cnt >= 0
  /\ cnt <= bound
  /\ (cnt = 0 => \E c \in Values : cand = c)

\* The .cfg also declares a liveness property (completion of the scan),
\* which is inherited from the main spec, so it is mentioned here as a note.
====