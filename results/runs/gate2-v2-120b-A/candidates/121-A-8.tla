---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANTS CharacterSet, Nat

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
MaxChar == MAX(CharacterSet)
LenBound == Nat

(*--------------------------------------------------------------------
  Sentinel value for undefined entries in the failure function.
  It is chosen outside the range of valid indices 0..2*LenBound .
--------------------------------------------------------------------*)
Sentinel == -1

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    str,        \* input string, a sequence of characters from CharacterSet
    Len,        \* length of the input string
    pi,         \* failure function array indexed 0..2*LenBound-1
    i,          \* pattern‑match index (current value from pi)
    k,          \* outer loop counter, runs from 1 to 2*Len
    offset,     \* current best rotation offset, 0..Len-1
    pc          \* program counter, one of the labels below

(*--------------------------------------------------------------------
  Labels for the program counter
--------------------------------------------------------------------*)
Labels == {"OuterCheck", "FailureLookup", "InnerLoop", "PostComparison",
           "Terminate", "Stutter"}

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
CircularChar(pos) == str[(pos % Len) + 1]   \* pos may be negative; +1 makes it 1‑based for Sequences

(*--------------------------------------------------------------------
  Init
--------------------------------------------------------------------*)
Init ==
    /\ Len \in 0..LenBound
    /\ Len = LenBound \/ Len \in 0..LenBound   \* any length up to the bound
    /\ Len = LenBound => Len \in 1..LenBound   \* non‑empty when we use the algorithm
    /\ Len = 0 => offset = 0                 \* degenerate case
    /\ Len > 0 => offset \in 0..Len-1
    /\ str \in [1..Len -> CharacterSet]
    /\ pi = [j \in 0..2*Len-1 |-> Sentinel]
    /\ i = Sentinel
    /\ k = 1
    /\ pc = "OuterCheck"

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF k < 2*Len
          THEN /\ pc' = "FailureLookup"
               /\ UNCHANGED <<str, Len, pi, i, k, offset>>
          ELSE /\ pc' = "Terminate"
               /\ UNCHANGED <<str, Len, pi, i, k, offset>>

FailureLookup ==
    /\ pc = "FailureLookup"
    /\ i' = pi[(k - offset + Len) % Len]   \* index into pi for position (k - offset) modulo Len
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<str, Len, pi, k, offset>>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ IF i # Sentinel
          THEN
               /\ IF CircularChar(k) = CircularChar(k - offset)
                     THEN /\ i' = i - 1
                          /\ pc' = "InnerLoop"
                     ELSE /\ IF CircularChar(k) < CircularChar(k - offset)
                              THEN offset' = k % Len
                              ELSE UNCHANGED offset
                          /\ i' = pi[i]   \* follow failure link
                          /\ pc' = "PostComparison"
          ELSE pc' = "PostComparison"
    /\ UNCHANGED <<str, Len, pi, k>>

PostComparison ==
    /\ pc = "PostComparison"
    /\ IF i = Sentinel
          THEN
               /\ IF CircularChar(k) # CircularChar(k - offset)
                     THEN /\ IF CircularChar(k) < CircularChar(k - offset)
                               THEN offset' = k % Len
                               ELSE UNCHANGED offset
                          /\ pi' = [pi EXCEPT ![(k - offset + Len) % Len] = i + 1]
                     ELSE pi' = pi
               /\ pc' = "Increment"
          ELSE pc' = "Increment"
    /\ UNCHANGED <<str, Len, i, k>>

Increment ==
    /\ pc = "Increment"
    /\ k' = k + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<str, Len, pi, i, offset>>

Terminate ==
    /\ pc = "Terminate"
    /\ pc' = "Stutter"
    /\ UNCHANGED <<str, Len, pi, i, k, offset>>

Stutter ==
    /\ pc = "Stutter"
    /\ UNCHANGED <<str, Len, pi, i, k, offset, pc>>

Next ==
    \/ OuterCheck
    \/ FailureLookup
    \/ InnerLoop
    \/ PostComparison
    \/ Increment
    \/ Terminate
    \/ Stutter

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<str, Len, pi, i, k, offset, pc>>

(*--------------------------------------------------------------------
  Type invariant (Safety)
--------------------------------------------------------------------*)
TypeInvariant ==
    /\ Len \in 0..LenBound
    /\ Len = 0 => offset = 0
    /\ Len > 0 => offset \in 0..Len-1
    /\ str \in [1..Len -> CharacterSet]
    /\ pi \in [0..2*Len-1 -> (0..2*Len-1) \cup {Sentinel}]
    /\ i \in (0..2*Len-1) \cup {Sentinel}
    /\ k \in 1..2*Len
    /\ pc \in Labels

(*--------------------------------------------------------------------
  Correctness invariant (Safety)
--------------------------------------------------------------------*)
Correctness ==
    /\ pc = "Terminate"
    /\ \A j \in 0..Len-1 :
          Rot(offset) <= Rot(j)
where Rot(pos) == 
        [m \in 0..Len-1 |-> CircularChar(pos + m)]

(*--------------------------------------------------------------------
  Termination (Liveness) – optional, not required as an INVARIANT
--------------------------------------------------------------------*)
Termination ==
    <>[] (pc = "Terminate")

====