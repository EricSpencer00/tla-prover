---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS A, B, C, bound

Values == { A, B, C }

VARIABLES seq, i, cand, count
vars == << seq, i, cand, count >>

\* A bounded version of Seq: only sequences up to a fixed length.
BoundedSeq(n) == UNION { { [ k \in 1..m -> Values ] : m \in 0..n } }

InitCand == CHOOSE v \in Values : TRUE

Init ==
  /\ seq \in BoundedSeq(bound)
  /\ i = 1
  /\ cand = InitCand
  /\ count = 0

\* One scan step of the Boyer-Moore majority vote algorithm.
Next ==
  /\ IF i <= Len(seq) THEN
       /\ IF count = 0 THEN
            /\ cand' = seq[i]
            /\ count' = 1
         ELSE IF seq[i] = cand THEN
            /\ count' = count + 1
         ELSE
            /\ count' = count - 1
       /\ i' = i + 1
     ELSE UNCHANGED << i, cand, count >>
  /\ UNCHANGED seq

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
  /\ seq \in BoundedSeq(bound)
  /\ i \in Nat
  /\ cand \in Values
  /\ count \in 0..3

\* After the scan finishes, any element that is a strict majority of the
\* sequence must equal the candidate -- the correctness condition.
Correct ==
  (i > Len(seq)) =>
    ( \A v \in Values : (2 * Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq))
                          => v = cand )

\* This inductive invariant mirrors the reasoning behind Boyer-Moore's
\* linear-time correctness proof.
Inv ==
  (i <= Len(seq)) =>
    ( (count > 0) =>
        ( \E s \in BoundedSeq(i - 1) :
            /\ \A j \in 1..(i - 1) : seq[j] = s[j]
            /\ \A v \in Values :
                 (2 * Cardinality({ j \in 1..(i - 1) : s[j] = v }) > (i - 1))
                   => v = cand ) )
  /\ (count = 0 => cand = InitCand)

Complete == i > Len(seq)

CompleteWeak == <>(Complete)

====