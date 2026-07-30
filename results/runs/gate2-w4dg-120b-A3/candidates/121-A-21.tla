---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

(* the character set must be a subset of Nat, but the config rewrites ZSequences *)
CONSTANTS
  CharacterSet

\* Types: the string is a sequence of characters, the failure function is an
\* array of indices into that sequence, and all other vars are bounded ints.
VARIABLES
  inputString, length, failure, matchIdx, loopCounter, bestOffset, pc

TypeInvariant ==
  /\ inputString \in Seq(CharacterSet)
  /\ length = Len(inputString)
  /\ failure \in [0..(2 * length) -> 0..(2 * length) \cup {0}]
  /\ matchIdx \in 0..(2 * length)
  /\ loopCounter \in 0..(2 * length)
  /\ bestOffset \in 0..(IF length = 0 THEN 0 ELSE length - 1)
  /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "UpdateBest",
        "FollowFailure", "PostCompare", "IncLoop", "Done"}

Init ==
  /\ inputString \in Seq(CharacterSet)
  /\ length = Len(inputString)
  /\ failure = [i \in 0..(2 * length) |-> 0]
  /\ matchIdx = 0
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "OuterCheck"

OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF loopCounter < (2 * length)
       THEN /\ pc' = "Lookup"
       ELSE /\ pc' = "Done"
  /\ UNCHANGED <<inputString, length, failure, matchIdx, loopCounter, bestOffset>>

Lookup ==
  /\ pc = "Lookup"
  /\ matchIdx' = failure[loopCounter]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<inputString, length, failure, loopCounter, bestOffset>>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ IF inputString[(loopCounter % length) + 1]
        = inputString[((bestOffset + matchIdx) % length) + 1]
       /\ matchIdx < length
     THEN /\ pc' = "UpdateBest"
          /\ matchIdx' = matchIdx + 1
     ELSE /\ pc' = "PostCompare"
  /\ UNCHANGED <<inputString, length, failure, loopCounter, bestOffset>>

UpdateBest ==
  /\ pc = "UpdateBest"
  /\ bestOffset' = IF inputString[(loopCounter % length) + 1]
                     < inputString[((bestOffset + matchIdx) % length) + 1]
                    THEN loopCounter % length
                    ELSE bestOffset
  /\ pc' = "FollowFailure"
  /\ UNCHANGED <<inputString, length, failure, matchIdx, loopCounter>>

FollowFailure ==
  /\ pc = "FollowFailure"
  /\ matchIdx' = failure[matchIdx]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<inputString, length, failure, loopCounter, bestOffset>>

PostCompare ==
  /\ pc = "PostCompare"
  /\ bestOffset' = IF matchIdx = 0
                    THEN IF inputString[(loopCounter % length) + 1]
                              < inputString[(bestOffset % length) + 1]
                         THEN loopCounter % length
                         ELSE bestOffset
                    ELSE bestOffset
  /\ failure' = [failure EXCEPT ![loopCounter] = IF matchIdx = 0
                                           THEN 0
                                           ELSE matchIdx + 1]
  /\ pc' = "IncLoop"
  /\ UNCHANGED <<inputString, length, matchIdx, loopCounter>>

IncLoop ==
  /\ pc = "IncLoop"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<inputString, length, failure, matchIdx, bestOffset>>

Stall ==
  /\ pc = "Done"
  /\ UNCHANGED <<inputString, length, failure, matchIdx, loopCounter, bestOffset, pc>>

Next == OuterCheck \/ Lookup \/ InnerLoop \/ UpdateBest
        \/ FollowFailure \/ PostCompare \/ IncLoop \/ Stall

Spec == Init /\ [][Next]_<<inputString, length, failure, matchIdx, loopCounter, bestOffset, pc>>

Rotate(s, k) ==
  LET n == Len(s) IN
    IF k = 0 THEN s
    ELSE
      [i \in 1..n |-> s[((i + k - 1) % n) + 1]]

Correctness ==
  /\ \A k \in 1..(IF length = 0 THEN 1 ELSE length) :
       Rotate(inputString, bestOffset) <= Rotate(inputString, k - 1)
  /\ \A k \in 0..(IF length = 0 THEN 0 ELSE length - 1) :
       (Rotate(inputString, bestOffset) = Rotate(inputString, k))
         => bestOffset <= k

Termination == <>(pc = "Done")
====