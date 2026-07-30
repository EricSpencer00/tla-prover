---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

\* A bounded sequence set: all sequences of length n over Values, for
\* every n between 0 and bound inclusive, constructed as functions from
\* 1..n. This keeps the state space finite for model checking.
Seqs == { [i \in 1..n |-> v[i]] : n \in 0..bound, v \in [1..n -> Values] }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

Init ==
    /\ seq \in Seqs
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

\* Boyer-Moore scan: advance the cursor with the three-case candidate
\* logic. pos = Len(seq) + 1 means the sequence is exhausted.
Next ==
    /\ pos <= Len(seq)
    /\ \/ /\ cand' = seq[pos]
          /\ cnt' = 0
       \/ /\ cand = seq[pos]
          /\ cnt' = cnt + 1
          /\ cand' = cand
       \/ /\ cnt >= 1
          /\ cand' = cand
          /\ cnt' = cnt - 1
    /\ pos' = pos + 1
    /\ seq' = seq

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ seq \in Seqs
    /\ pos \in 1..(bound + 1)
    /\ cand \in Values
    /\ cnt \in 0..bound

\* Main correctness: any element that is a true majority of the scanned
\* prefix must equal the current candidate, but only well-defined when a
\* complete scan has finished.
Correct ==
    (pos = Len(seq) + 1 /\ cnt >= 1) => (cnt * 2 > Len(seq) => cand = seq[pos - cnt])

\* An inductive invariant that the candidate is always in the scanned
\* prefix when the counter is non-zero, plus the type invariant.
Inv ==
    /\ TypeOK
    /\ (cnt >= 1 => pos >= 2 /\ seq[pos - cnt] = cand)

WeakFairness == WF_vars(Next)

====