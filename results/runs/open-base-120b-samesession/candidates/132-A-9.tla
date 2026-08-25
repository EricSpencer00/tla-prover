---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT A, B, C, bound

\* The set of possible element values
Values == { A, B, C }

\* Bounded version of Seq to keep the state space finite
BoundedSeq == { s \in Seq(Values) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

vars == << seq, i, cand, cnt >>

\* Initial state
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

\* One step of the Boyer‑Moore scan
Next ==
    \/ /\ i <= Len(seq)
       /\ LET x == seq[i] IN
          IF cnt = 0 THEN
              /\ cand' = x
              /\ cnt' = 1
          ELSE IF cand = x THEN
              /\ cand' = cand
              /\ cnt' = cnt + 1
          ELSE
              /\ cand' = cand
              /\ cnt' = cnt - 1
       /\ i' = i + 1
       /\ UNCHANGED seq
    \/ /\ i > Len(seq)
       /\ UNCHANGED << seq, i, cand, cnt >>

\* Full specification (includes weak fairness for liveness)
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

\* Helper: count occurrences of a value in a sequence
Count(v, s) ==
    Cardinality({ j \in 1..Len(s) : s[j] = v })

\* Definition of a majority element in the current sequence
Majority(v) ==
    Count(v, seq) > Len(seq) \div 2

\* Safety property: after the scan any true majority must equal the candidate
Correct ==
    (i > Len(seq)) => ( \A v \in Values : Majority(v) => cand = v )

\* An inductive invariant (example)
Inv ==
    /\ cnt <= Len(seq)
    /\ (cnt = 0 => cand \in Values)

====