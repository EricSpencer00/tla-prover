---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences

CONSTANTS CharacterSet, Nat

Uninitialized == -1

VARIABLES inputString, length, failure, pattern, loopCounter, bestOffset, pc

vars == <<inputString, length, failure, pattern, loopCounter, bestOffset, pc>>

\* The algorithm treats the string as a doubled circular sequence of length
\* 2 * length, indexing characters by position modulo length. The failure
\* function (failure) is KMP-style; pattern is the current failure index.
\* The loop counter (loopCounter) runs the outer loop up to 2 * length.
\* At every step the program counter pc names the next labeled step to run.
\* The string itself is chosen nondeterministically from all zero-indexed
\* sequences over the character set (the corpus).

CharacterSequences ==
  { s \in Seq(CharacterSet) : Len(s) <= Nat }

\* Lexicographic ordering of a rotated zero-indexed string. We compare
\* character by character, wrapping around at the end of the string.
LEq(s, off1, off2) ==
  LET n == Len(s) IN
  \A k \in 0 .. (n - 1) :
    LET i1 == (off1 + k) % n
        i2 == (off2 + k) % n
    IN
      IF s[i1] < s[i2] THEN TRUE
      ELSE IF s[i1] > s[i2] THEN FALSE
      ELSE TRUE

Init ==
  /\ inputString \in CharacterSequences
  /\ length = Len(inputString)
  /\ failure \in [0 .. (2 * Nat)] -> (0 .. Nat) \cup {Uninitialized}
  /\ pattern = Uninitialized
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ loopCounter < (2 * length)
  /\ pc' = "failureLookup"
  /\ UNCHANGED <<inputString, length, failure, pattern, loopCounter, bestOffset>>

\* Failure function lookup: step (2) in the description.
FailureLookup ==
  /\ pc = "failureLookup"
  /\ failure' = [failure EXCEPT ![loopCounter - bestOffset] = pattern]
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, length, pattern, loopCounter, bestOffset>>

\* Step (3): the inner character comparison loop.
Compare ==
  /\ pc = "compare"
  /\ LET cur == inputString[(loopCounter % length)]
         cand == inputString[((loopCounter - bestOffset) % length)]
     IN
       IF cur # cand
         /\ pattern # Uninitialized
         THEN pc' = "compare"
         ELSE pc' = "postCompare"
  /\ UNCHANGED <<inputString, length, failure, pattern, loopCounter, bestOffset>>

\* Step (4): a strict improvement: the current rotation beats the best so
\* far, so the best rotation offset is updated.
UpdateOnImprovement ==
  /\ pc = "compare"
  /\ pattern # Uninitialized
  /\ LET cur == inputString[(loopCounter % length)]
         cand == inputString[((loopCounter - bestOffset) % length)]
     IN cur < cand
  /\ bestOffset' = loopCounter - bestOffset
  /\ UNCHANGED <<inputString, length, failure, pattern, loopCounter, pc>>

\* Step (5): follow the failure function chain.
FollowFailure ==
  /\ pc = "compare"
  /\ pattern # Uninitialized
  /\ pattern' = failure[pattern]
  /\ UNCHANGED <<inputString, length, failure, loopCounter, bestOffset, pc>>

\* Step (6): after the inner loop has exhausted (no improvement that
\* follows an existing failure chain), decide definitively whether the
\* current rotation is a strict improvement, and fill in the failure
\* function for the current position.
PostCompare ==
  /\ pc = "postCompare"
  /\ LET cur == inputString[(loopCounter % length)]
         cand == inputString[((loopCounter - bestOffset) % length)]
         newOffset == IF cur < cand THEN (loopCounter - bestOffset) ELSE bestOffset
         pattern' == IF pattern = Uninitialized THEN Uninitialized ELSE pattern
         newValue == IF pattern = Uninitialized THEN Uninitialized ELSE (1 + pattern)
     IN /\ bestOffset' = newOffset
        /\ failure' = [failure EXCEPT ![loopCounter - bestOffset] = newValue]
        /\ pattern' \in (0 .. Nat) \cup {Uninitialized}
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, length, loopCounter>>

\* Step (7): advance the outer loop counter and return to the top.
Increment ==
  /\ pc = "increment"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<inputString, length, failure, pattern, bestOffset>>

Terminated ==
  /\ pc = "outerCheck"
  /\ loopCounter >= (2 * length)
  /\ UNCHANGED vars

Stall ==
  /\ Terminated
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ FailureLookup
  \/ Compare
  \/ UpdateOnImprovement
  \/ FollowFailure
  \/ PostCompare
  \/ Increment
  \/ Terminated
  \/ Stall

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ inputString \in CharacterSequences
  /\ length = Len(inputString)
  /\ failure \in [0 .. (2 * Nat)] -> (0 .. Nat) \cup {Uninitialized}
  /\ pattern \in (0 .. Nat) \cup {Uninitialized}
  /\ loopCounter \in 0 .. (2 * Nat)
  /\ bestOffset \in 0 .. Nat
  /\ pc \in {"outerCheck", "failureLookup", "compare", "postCompare", "increment"}

\* Correctness: at termination the best rotation is the lexicographically
\* minimal rotation of the input string, and among rotations that compare
\* equal it is the one with the smallest shift.
Correctness ==
  Terminated => (LEq(inputString, bestOffset, 0) /\ \A k \in 1 .. (length - 1) : LEq(inputString, bestOffset, k))

Termination == <>(pc = "outerCheck" /\ loopCounter >= (2 * length))

====