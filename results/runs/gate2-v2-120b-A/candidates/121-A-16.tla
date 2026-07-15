---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANT CharacterSet      \* A finite subset of Nat, supplied by the .cfg
CONSTANT Nat               \* The set of natural numbers (provided by Naturals)

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
Sentinel == -1

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    inputStr,          \* The circular string (a sequence of characters)
    n,                 \* Length of inputStr
    failure,           \* Failure function array, indices 0..2*n
    pi,                \* Pattern-match index
    i,                 \* Outer loop counter, runs from 1 to 2*n
    best,              \* Best rotation offset (0..n-1)
    pc                 \* Program counter (labels the current step)

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Chars == CharacterSet

InputSeq == [i \in 0..n-1 |-> inputStr[i]]

CircularChar(pos) == inputStr[pos % n]

\* Returns the character at position (offset + k) modulo n
CharAt(offset, k) == inputStr[(offset + k) % n]

\* Lexicographic comparison of two rotations
RotLessThan(off1, off2) ==
    \E k \in 0..n-1 :
        /\ \A j \in 0..k-1 : CharAt(off1, j) = CharAt(off2, j)
        /\ CharAt(off1, k) < CharAt(off2, k)

\* Equality of two rotations (used for tie‑breaking)
RotEqual(off1, off2) ==
    \A k \in 0..n-1 : CharAt(off1, k) = CharAt(off2, k)

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
    /\ inputStr \in Seq(Chars)            \* nondeterministically chosen
    /\ n = Len(inputStr)
    /\ n > 0                               \* avoid empty strings
    /\ failure = [j \in 0..2*n |-> Sentinel]
    /\ pi = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

(*-----------------------------------------------------------------
  Actions (labelled steps)
-----------------------------------------------------------------*)
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i >= 2*n
          THEN /\ pc' = "Terminated"
               /\ UNCHANGED <<inputStr, n, failure, pi, i, best>>
          ELSE /\ pc' = "Lookup"
               /\ UNCHANGED <<inputStr, n, failure, pi, i, best>>
    /\ i' = i

Lookup ==
    /\ pc = "Lookup"
    /\ pi' = failure[(i - best) % n]          \* index into failure using current offset
    /\ pc' = "InnerCompare"
    /\ UNCHANGED <<inputStr, n, failure, i, best>>

InnerCompare ==
    /\ pc = "InnerCompare"
    /\ IF (pi = Sentinel) \/ (CircularChar(i) # CharAt(best, pi + 1))
          THEN /\ pc' = "PostCompare"
               /\ UNCHANGED pi
          ELSE /\ /\ CircularChar(i) = CharAt(best, pi + 1)
               /\ pi' = pi + 1
               /\ pc' = "InnerCompare"
    /\ UNCHANGED <<inputStr, n, failure, i, best>>

PostCompare ==
    /\ pc = "PostCompare"
    /\ IF (pi = Sentinel) \/ (CircularChar(i) # CharAt(best, pi + 1))
          THEN /\ IF CircularChar(i) < CharAt(best, pi + 1)
                    THEN /\ best' = i % n
                         /\ UNCHANGED <<inputStr, n, failure, pi>>
                    ELSE /\ best' = best
                         /\ UNCHANGED <<inputStr, n, failure, pi>>
               /\ failure[(i - best) % n]' = IF pi = Sentinel THEN 1 ELSE pi + 1
               /\ pc' = "Increment"
          ELSE /\ pc' = "FollowFailure"
               /\ UNCHANGED <<inputStr, n, failure, best>>
    /\ UNCHANGED i

FollowFailure ==
    /\ pc = "FollowFailure"
    /\ pi' = failure[pi]                     \* follow the failure chain
    /\ pc' = "InnerCompare"
    /\ UNCHANGED <<inputStr, n, failure, i, best>>

Increment ==
    /\ pc = "Increment"
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<inputStr, n, failure, pi, best>>

Stutter ==
    /\ pc = "Terminated"
    /\ UNCHANGED <<inputStr, n, failure, pi, i, best, pc>>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerCompare
    \/ PostCompare
    \/ FollowFailure
    \/ Increment
    \/ Stutter

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<inputStr, n, failure, pi, i, best, pc>>

(*-----------------------------------------------------------------
  Type invariant (all variables stay within their intended domains)
-----------------------------------------------------------------*)
TypeInvariant ==
    /\ inputStr \in Seq(Chars)
    /\ n = Len(inputStr)
    /\ n > 0
    /\ failure \in [0..2*n -> (0..n) \cup {Sentinel}]
    /\ pi \in (0..n) \cup {Sentinel}
    /\ i \in 1..2*n
    /\ best \in 0..n-1
    /\ pc \in {"OuterCheck", "Lookup", "InnerCompare",
               "PostCompare", "FollowFailure", "Increment", "Terminated"}

(*-----------------------------------------------------------------
  Correctness invariant: best points to the lexicographically minimal rotation
-----------------------------------------------------------------*)
Correctness ==
    /\ \A offset \in 0..n-1 :
          RotLessThan(best, offset) \/ RotEqual(best, offset)

=============================================================================