---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet, Nat

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Char == CharacterSet
Str  == Seq(Char)

\* Sentinel value for undefined entries in the failure function
Sentinel == -1

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES input,          \* the original string (zero‑indexed)
          n,              \* its length
          failure,        \* array indexed 0..2*n, values = -1 or 0..2*n
          p,              \* pattern‑match index (may be -1)
          i,              \* outer loop counter (1..2*n)
          best,           \* best rotation offset (0..n-1)
          pc              \* program counter (labels of the algorithm)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Index modulo n, defined for all natural numbers (even when n = 0)
Mod(i) == IF n = 0 THEN 0 ELSE i % n

\* Character at position j of the circular view of the string
CharAt(j) == input[ Mod(j) + 1 ]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ input \in Str
    /\ n = Len(input)
    /\ failure = [k \in 0..2*n |-> Sentinel]
    /\ p = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Actions (each labelled by the program counter)
\* ----------------------------------------------------------------------
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i >= 2*n
          THEN /\ pc' = "Terminated"
               /\ UNCHANGED << input, n, failure, p, i, best >>
          ELSE /\ pc' = "FailureLookup"
               /\ UNCHANGED << input, n, failure, p, i, best >>

FailureLookup ==
    /\ pc = "FailureLookup"
    /\ p' = failure[ i - best ]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED << input, n, failure, i, best >>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ IF p # Sentinel
          THEN /\ IF CharAt(i) = CharAt(best + p + 1)
                    THEN /\ p' = p + 1
                         /\ pc' = "InnerLoop"
                         /\ UNCHANGED << input, n, failure, i, best >>
                    ELSE /\ IF CharAt(i) < CharAt(best + p + 1)
                              THEN /\ best' = Mod(i - p)
                                   /\ UNCHANGED << input, n, failure, i, p >>
                              ELSE UNCHANGED << input, n, failure, i, p, best >>
                         /\ pc' = "FollowFailure"
          ELSE /\ pc' = "PostComp"
               /\ UNCHANGED << input, n, failure, i, p, best >>

FollowFailure ==
    /\ pc = "FollowFailure"
    /\ p' = failure[p]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED << input, n, failure, i, best >>

PostComp ==
    /\ pc = "PostComp"
    /\ IF CharAt(i) # CharAt(best + p + 1)
          THEN /\ IF p = Sentinel
                    THEN /\ IF CharAt(i) < CharAt(best + p + 1)
                              THEN best' = Mod(i - p)
                              ELSE UNCHANGED best
                         /\ failure' = [failure EXCEPT ![i - best] = Sentinel]
                    ELSE /\ IF CharAt(i) # CharAt(best + p + 1)
                              THEN best' = best
                              ELSE best' = best
                         /\ failure' = [failure EXCEPT ![i - best] = p + 1]
               /\ pc' = "Inc"
          ELSE /\ failure' = [failure EXCEPT ![i - best] = p + 1]
               /\ pc' = "Inc"
    /\ UNCHANGED << input, n, i, p >>

Inc ==
    /\ pc = "Inc"
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED << input, n, failure, p, best >>

Terminated ==
    /\ pc = "Terminated"
    /\ UNCHANGED << input, n, failure, p, i, best, pc >>

Stutter ==
    /\ pc = "Terminated"
    /\ UNCHANGED << input, n, failure, p, i, best, pc >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ OuterCheck
    \/ FailureLookup
    \/ InnerLoop
    \/ FollowFailure
    \/ PostComp
    \/ Inc
    \/ Terminated
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<input, n, failure, p, i, best, pc>>

\* ----------------------------------------------------------------------
\* Type invariant (ensures all variables stay within their domains)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ input \in Str
    /\ n = Len(input)
    /\ failure \in [0..2*n -> (Sentinel \cup 0..2*n)]
    /\ p \in Sentinel \cup 0..2*n
    /\ i \in 1..2*n + 1            \* i may reach 2*n+1 in the terminated state
    /\ best \in 0..n-1
    /\ pc \in {"OuterCheck","FailureLookup","InnerLoop",
                "FollowFailure","PostComp","Inc","Terminated"}

\* ----------------------------------------------------------------------
\* Correctness invariant: best is the offset of the lexicographically
\* smallest rotation of the input string.
\* ----------------------------------------------------------------------
RotationAt(off) == 
    IF n = 0 THEN <<>>
    ELSE << CharAt(off + k) : k \in 0..n-1 >>

Correctness ==
    /\ best \in 0..n-1
    /\ \A off \in 0..n-1 :
          RotationAt(best) <= RotationAt(off)

\* ----------------------------------------------------------------------
\* The required properties as named in the .cfg
\* ----------------------------------------------------------------------
Invariant == TypeInvariant /\ Correctness

\* ----------------------------------------------------------------------
\* Theorems (optional, but keep the identifiers for the .cfg)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []Correctness

====