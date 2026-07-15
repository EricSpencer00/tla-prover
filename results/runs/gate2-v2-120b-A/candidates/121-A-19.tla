---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CharacterSet, Nat \* Nat is the sentinel index (must be > any valid index)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
NatSentinel == Nat          \* sentinel value used in the algorithm

\* Zero‑indexed modulo operation (returns a value in 0..len-1)
Mod(i, len) == i % len

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    s,          \* input string: a sequence of characters (0‑indexed)
    n,          \* length of s
    failure,    \* failure function array indexed from 0 to 2*n, values in NatSentinel ∪ 0..2*n
    i,          \* pattern‑match index (or NatSentinel)
    j,          \* outer loop counter, runs from 1 to 2*n
    offset,     \* best rotation offset found so far (0..n-1)
    pc          \* program counter: one of the labeled steps or "Done"

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ s \in [0..] -> CharacterSet                \* any zero‑indexed sequence over the alphabet
    /\ n = Len(s)
    /\ failure = [k \in 0..2*n |-> NatSentinel]
    /\ i = NatSentinel
    /\ j = 1
    /\ offset = 0
    /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Actions (labeled steps of Booth's algorithm)
\* ----------------------------------------------------------------------
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF j >= 2*n
          THEN /\ pc' = "Done"
               /\ UNCHANGED <<s, n, failure, i, j, offset>>
          ELSE /\ pc' = "LookupFailure"
               /\ UNCHANGED <<s, n, failure, i, j, offset>>

LookupFailure ==
    /\ pc = "LookupFailure"
    /\ i' = failure[ offset + j ]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<s, n, failure, j, offset>>

InnerLoop ==
    /\ pc = "InnerLoop"
    LET cur  == s[ Mod(j, n) ]                \* character at current outer position
        cand == s[ Mod(offset + j, n) ]       \* character at candidate rotation
    IN
    IF cur = cand
        THEN /\ i' = i + 1
             /\ IF i' = n
                   THEN /\ pc' = "Done"          \* all characters matched; algorithm can stop early
                        /\ UNCHANGED <<s, n, failure, j, offset>>
                   ELSE /\ pc' = "InnerLoop"
                        /\ UNCHANGED <<s, n, failure, j, offset>>
        ELSE IF i /= NatSentinel
                THEN /\ pc' = "FollowFailure"
                     /\ UNCHANGED <<s, n, failure, j, offset, i>>
                ELSE /\ pc' = "PostCompare"
                     /\ UNCHANGED <<s, n, failure, j, offset, i>>

FollowFailure ==
    /\ pc = "FollowFailure"
    /\ i' = failure[i]               \* follow the failure link
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<s, n, failure, j, offset>>

PostCompare ==
    /\ pc = "PostCompare"
    LET cur  == s[ Mod(j, n) ]
        cand == s[ Mod(offset + j, n) ]
    IN
    IF cur < cand
        THEN /\ offset' = j
        ELSE /\ offset' = offset
    /\ failure[ offset + j ]' =
          IF i = NatSentinel
             THEN NatSentinel
             ELSE i + 1
    /\ pc' = "Increment"
    /\ UNCHANGED <<s, n, i, j>>

Increment ==
    /\ pc = "Increment"
    /\ j' = j + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<s, n, failure, i, offset>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<s, n, failure, i, j, offset, pc>>

\* Stuttering action to keep the model from deadlocking after termination
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<s, n, failure, i, j, offset, pc>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ OuterCheck
    \/ LookupFailure
    \/ InnerLoop
    \/ FollowFailure
    \/ PostCompare
    \/ Increment
    \/ Done
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<s, n, failure, i, j, offset, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ s \in [0..] -> CharacterSet
    /\ n = Len(s)
    /\ failure \in [0..2*n -> NatSentinel \cup 0..2*n]
    /\ i \in NatSentinel \cup 0..2*n
    /\ j \in 1..2*n + 1
    /\ offset \in 0..n-1
    /\ pc \in {"OuterCheck", "LookupFailure", "InnerLoop",
                "FollowFailure", "PostCompare", "Increment",
                "Done"}

\* Correctness: offset yields the lexicographically minimal rotation
Correctness ==
    \A k \in 0..n-1 :
        LET rotOff == [i \in 0..n-1 |-> s[ Mod(offset + i, n) ]]
            rotK   == [i \in 0..n-1 |-> s[ Mod(k      + i, n) ]]
        IN  LexLeq(rotOff, rotK)

\* Lexicographic ≤ on two zero‑indexed sequences of equal length
LexLeq(seq1, seq2) ==
    \A i \in 0..n-1 :
        ( \A j \in 0..i-1 : seq1[j] = seq2[j] ) => seq1[i] <= seq2[i]

\* ----------------------------------------------------------------------
\* Optional theorem (not required by the .cfg but useful for TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []Correctness

====