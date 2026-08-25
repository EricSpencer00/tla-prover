---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

VARIABLES seq, i, cand, cnt

\* The set of possible element values
Value == { A, B, C }

\* A finite version of Seq: all sequences over S whose length is at most *bound*
BoundedSeq(S) ==
  UNION { [j \in 1..n -> S] : n \in 0..bound }

\* Type correctness invariant
TypeOK ==
  /\ seq \in BoundedSeq(Value)
  /\ i \in Nat
  /\ cnt \in Nat
  /\ cand \in Value

\* Initial state
Init ==
  /\ seq \in BoundedSeq(Value)
  /\ i = 1
  /\ cnt = 0
  /\ cand \in Value

\* One step of the Boyer‑Moore scan
Next ==
  \/ /\ i <= Len(seq)
     /\ LET x == seq[i] IN
        \/ /\ cnt = 0
           /\ cand' = x
           /\ cnt' = 1
        \/ /\ cnt > 0 /\ cand = x
           /\ cand' = cand
           /\ cnt' = cnt + 1
        \/ /\ cnt > 0 /\ cand # x
           /\ cand' = cand
           /\ cnt' = cnt - 1
     /\ i' = i + 1
     /\ UNCHANGED seq
  \/ /\ i > Len(seq)
     /\ UNCHANGED <<seq, i, cand, cnt>>

\* Full specification (initial condition and always‑next)
Spec ==
  Init /\ [][Next]_<<seq, i, cand, cnt>>

\* Majority predicate for a value *v*
Majority(v) ==
  /\ v \in Value
  /\ Card({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq) / 2

\* Safety property: any true majority must equal the final candidate
Correct ==
  (i > Len(seq)) => \A v \in Value : (Majority(v) => v = cand)

\* Inductive invariant (here we simply reuse the type invariant)
Inv ==
  TypeOK

====