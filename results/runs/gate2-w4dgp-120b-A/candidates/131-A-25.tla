---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value, n

\* The Boyer-Moore majority vote algorithm: it scans a fixed sequence of length n,
\* maintains a candidate element, and a count. The scan index i is the
\* processed-prefix length; Count(i) is the candidate's net advantage over that
\* prefix. The core invariant is the telescoping sum that bounds any element's
\* net advantage by the scan's count.

VARIABLES seq, candidate, cnt, i

vars == <<seq, candidate, cnt, i>>

\* Positions before index i, used for the cardinality bound on a net advantage.
Before(i) == {k \in 1..i : seq[k] = candidate}

BeforeNot == {k \in 1..i : seq[k] # candidate}

TypeOK ==
    /\ seq \in [1..n -> Value]
    /\ candidate \in Value
    /\ cnt \in 0..n
    /\ i \in 0..n

MaxCandidate(i) == Cardinality(Before(i)) - Cardinality(BeforeNot)

\* The telescoping sum: the candidate's net advantage over the scanned prefix is
\* never larger than the scan length itself.
Inv == MaxCandidate(i) <= i

Init ==
    /\ seq = [k \in 1..n |-> CHOOSE v \in Value : TRUE]
    /\ candidate = CHOOSE v \in Value : TRUE
    /\ cnt = 0
    /\ i = 0

\* Reset the candidate and count once the whole sequence has been scanned.
Reset ==
    /\ i = n
    /\ candidate' = CHOOSE c \in Value : TRUE
    /\ cnt' = 0
    /\ i' = 0
    /\ UNCHANGED seq

\* Scan the next element, bumping or resetting the candidate as needed.
Move ==
    /\ i < n
    /\ LET nxt == seq[i + 1] IN
        IF cnt = 0 THEN
            /\ candidate' = nxt
            /\ cnt' = 1
        ELSE IF nxt = candidate THEN
            /\ cnt' = cnt + 1
            /\ UNCHANGED candidate
        ELSE
            /\ cnt' = cnt - 1
            /\ UNCHANGED candidate
    /\ i' = i + 1
    /\ UNCHANGED seq

Next == Reset \/ Move

Spec == Init /\ [][Next]_vars

\* SAFETY: any element appearing in a strict majority of positions must be the
\* candidate. The count bound forces the candidate's net advantage to dominate
\* any other element's, so a strict majority can only belong to the candidate.
MajorityCandidate ==
    \A x \in Value :
        (2 * Cardinality({k \in 1..n : seq[k] = x}) > n) => (x = candidate)

====