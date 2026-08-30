---- MODULE MajorityProof ----
EXTENDS Integers, Sequences, FiniteSets, MajorityVote

CONSTANTS Value

\* No new state; all variables are from MajorityVote.
VARIABLES candidate, seenCount, seenTotal, i, seq

vars == <<candidate, seenCount, seenTotal, i, seq>>

TypeOK ==
    /\ candidate \in Value \cup {"none"}
    /\ seenCount \in Nat
    /\ seenTotal \in Nat
    /\ i \in Nat
    /\ seq \in Seq(Value)

Init ==
    /\ candidate = "none"
    /\ seenCount = 0
    /\ seenTotal = 0
    /\ i = 0
    /\ seq = << >>

\* Matches the candidate so far and advances the majority count with it.
Match ==
    /\ i < Len(seq)
    /\ seq[i + 1] = candidate
    /\ seenCount' = seenCount + 1
    /\ i' = i + 1
    /\ UNCHANGED <<candidate, seenTotal, seq>>

\* The candidate cannot be set to a new value partway through the pass.
SetCandidate ==
    /\ candidate = "none"
    /\ candidate' = seq[i + 1]
    /\ seenCount' = seenCount + 1
    /\ i' = i + 1
    /\ UNCHANGED <<seenTotal, seq>>

\* Seen a value that does not match the candidate: count it against the
\* majority tally.
Mismatch ==
    /\ i < Len(seq)
    /\ (candidate # "none" /\ seq[i + 1] # candidate)
    /\ i' = i + 1
    /\ UNCHANGED <<candidate, seenCount, seenTotal, seq>>

\* Read the next input value into the sequence.
ReadHead ==
    /\ i = 0
    /\ seq' = seq \o <<CHOOSE v \in Value: TRUE>>
    /\ UNCHANGED <<candidate, seenCount, seenTotal, i>>

\* Only run the mismatch case once the whole sequence has been consumed.
Retry ==
    /\ i = Len(seq)
    /\ UNCHANGED vars

Next == Match \/ SetCandidate \/ Mismatch \/ ReadHead \/ Retry

Spec == Init /\ [][Next]_vars

\* The per-position tally on the candidate stays within the scanned prefix.
SeenCountWithinPrefix ==
    /\ seenCount <= i
    /\ seenCount = Cardinality({j \in 1..i : seq[j] = candidate})

\* The strict-majority guarantee is the algorithm's output: a majority value
\* must equal the candidate at the end of the pass.
MajorityCandidate == Inv /\ Correct
====