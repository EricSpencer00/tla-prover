---- MODULE MCMajority -----------------------------------------------
EXTENDS Integers, Sequences, FiniteSets

\* The three possible values for the majority‑vote algorithm.
CONSTANTS A, B, C

\* Upper bound on the length of the sequence (must be a natural number).
CONSTANT bound

\* The set of admissible values.
Value == {A, B, C}

\* All sequences over Value whose length is at most bound.
BoundedSeq == { s \in [1..n -> Value] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

\* Initial state: a non‑empty sequence of length at most bound, the
\* candidate and counter are derived from that sequence.
Init ==
    /\ i = Len(seq)
    /\ i = 0 \/ cnt > 0
    /\ /\ i = 0 => cand = A   \* arbitrary value when the sequence is empty
       /\ i > 0 => cand = seq[i]

\* The one‑step action of the classic Boyer‑Moore majority vote algorithm.
Step ==
    /\ i > 0
    /\ IF i = 1
          THEN /\ cand' = seq[1]
               /\ cnt'  = 1
          ELSE IF cnt = 0
                  THEN /\ cand' = seq[i-1]
                       /\ cnt'  = 1
                  ELSE IF seq[i-1] = cand
                          THEN /\ cnt' = cnt + 1
                               /\ cand' = cand
                          ELSE /\ cnt' = cnt - 1
                               /\ cand' = cand
    /\ i' = i - 1

\* The algorithm terminates when all positions have been processed.
Terminate == i = 0

\* Safety invariant: when the algorithm has finished,
\* either the sequence is empty or the candidate appears more often
\* than any other element.
SafetyInvariant ==
    /\ i = 0
    /\ ( Len(seq) = 0
        \/ \A v \in Value : 
            Cardinality({ j \in 1..Len(seq) : seq[j] = cand }) >
            Cardinality({ j \in 1..Len(seq) : seq[j] = v }) )

\* Optional: a trivial type invariant to keep TLC happy.
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in 0..Bound
    /\ cnt \in Nat
    /\ cand \in Value

vars == << seq, i, cand, cnt >>

\* The specification
Spec == Init /\ [][Step]_vars

====