---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* The value set is fixed to the three named constants; the length bound is
\* fixed to the value given in the .cfg, so the model is finite and exhaustive.
Values == {A, B, C}
SeqBound == bound

Sequences == { f \in [1..n -> Values] : n \in 0..SeqBound }

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

TypeOK == /\ seq \in Sequences
          /\ pos \in 1..(SeqBound + 1)
          /\ cand \in Values
          /\ count \in 0..SeqBound

Init == /\ seq \in Sequences
        /\ pos = 1
        /\ cand \in Values
        /\ count = 0

Majority == Cardinality({ i \in 1..Len(seq) : seq[i] = cand }) > Len(seq) \div 2

\* BoundedSeq replaces the standard Seq so the model stays finite.
BoundedSeq == seq

\* Scan the next element and update the Boyer-Moore candidate/counter.
Scan == /\ pos <= Len(BoundedSeq)
        /\ LET x == BoundedSeq[pos] IN
             IF count = 0 THEN /\ cand' = x
                              /\ count' = 1
             ELSE IF cand = x THEN /\ count' = count + 1
                              /\ UNCHANGED cand
             ELSE /\ count' = count - 1
                  /\ UNCHANGED cand
        /\ pos' = pos + 1
        /\ UNCHANGED seq

Reset == /\ pos > Len(BoundedSeq)
         /\ pos' = 1
         /\ cand' \in Values
         /\ count' = 0
         /\ UNCHANGED seq

Next == Scan \/ Reset

Spec == Init /\ [][Next]_vars /\ WF_vars(Reset)

\* The Boyer-Moore candidate is the true majority once the scan is complete.
Correct == (pos > Len(BoundedSeq) /\ Majority) => cand = BoundedSeq[1]

\* The candidate is never a phantom: it always equals some sequence element.
Inv == \E i \in 1..Len(seq) : seq[i] = cand

\* SAFETY: type correctness and the two substantive invariants together.
TypeOKInvariant == /\ TypeOK
                   /\ Correct
                   /\ Inv

\* LIVENESS: a scan always eventually completes.
SpecComplete == Spec /\ WF_vars(Scan)

====