---- MODULE MCMajority ----
EXTENDS Naturals

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

VARIABLES seq, pos, cand, count
vars == <<seq, pos, cand, count>>

\* A bounded sequence is a function from a prefix of the naturals (starting at 1)
\* to Values whose domain is contiguous and does not exceed the bound.
SeqBounded == {s \in Seq : s # [x \in 1..bound |-> A] /\ s \in [1..Len(s) -> Values]}

\* Inherited actions: scanning the next element with the Boyer-Moore three-case logic.
ScanA(s) == Count(s, cand)
ScanB(s) == IF cand = A THEN cand' = B ELSE cand' = A
ScanC(s) == IF cand = B THEN cand' = A ELSE cand' = C

\* A step: advance the scan position by one and update candidate/counter according
\* to the next element, or idle once the scan reaches the end of the sequence.
NextStep(s) ==
    \/ \E e \in Values : ScanA(e) /\ count' = count + 1
    \/ ScanB(s) /\ count' = count - 1
    \/ ScanC(s)
    \/ IF pos > Len(seq) THEN UNCHANGED <<seq, pos, cand, count>> ELSE UNCHANGED vars

Init ==
    /\ seq \in SeqBounded
    /\ pos = 1
    /\ \E v \in Values : cand = v
    /\ count = 0

Next ==
    \E s \in Values : NextStep(s)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E s \in Values : NextStep(s))

TypeOK ==
    /\ seq \in SeqBounded
    /\ pos \in 0..bound
    /\ cand \in Values
    /\ count \in -bound..bound

\* The main correctness property: any true majority element must equal the
\* candidate after a full scan -- only meaningful once the scan is complete.
Correct ==
    (pos = Len(seq) + 1) => (\A v \in Values : 2 * Count(seq, v) > Len(seq) => v = cand)

Inv == TypeOK

====