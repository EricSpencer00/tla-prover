---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet, Nat

\* The sentinel value for an undefined failure-function entry.
\* It is chosen outside the range of valid indices.
Sentinel == Nat

VARIABLES inputString, length, failure, matchIdx, loop, bestOffset, pc

vars == <<inputString, length, failure, matchIdx, loop, bestOffset, pc>>

\* The corpus: every zero-indexed sequence over the character set up to
\* the configured maximum length.
Corpus == { s \in Seq(CharacterSet) : Len(s) <= Nat }

TypeInvariant ==
  /\ inputString \in Corpus
  /\ length = Len(inputString)
  /\ failure \in [0..(2 * length) -> 0..Nat]
  /\ matchIdx \in 0..Nat
  /\ loop \in 1..(2 * length)
  /\ bestOffset \in 0..(length - 1)
  /\ pc \in {"outerCheck", "lookup", "innerLoop", "updateBest",
             "followChain", "postCompare", "increment", "done"}

Init ==
  /\ inputString \in Corpus
  /\ length = Len(inputString)
  /\ failure = [i \in 0..(2 * length) |-> Sentinel]
  /\ matchIdx = Sentinel
  /\ loop = 1
  /\ bestOffset = 0
  /\ pc = "outerCheck"

\* Outer loop: run up to twice the string length to cover the doubled
\* string without explicit circular indexing.
OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF loop < (2 * length) THEN pc' = "lookup" ELSE pc' = "done"
  /\ UNCHANGED <<inputString, length, failure, matchIdx, loop, bestOffset>>

Lookup ==
  /\ pc = "lookup"
  /\ matchIdx' = failure[loop - 1]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, length, failure, loop, bestOffset>>

\* Compare the character at the current loop position with the
\* character at the candidate position offset by the best rotation.
InnerLoop ==
  /\ pc = "innerLoop"
  /\ LET curChar == inputString[(loop % length)]
         candChar == inputString[(bestOffset + loop) % length]
     IN
       /\ IF curChar = candChar
            THEN pc' = "postCompare"
            ELSE IF matchIdx # Sentinel
                 THEN pc' = "updateBest"
                 ELSE pc' = "postCompare"
       /\ UNCHANGED <<inputString, length, failure, matchIdx, loop, bestOffset>>

UpdateBest ==
  /\ pc = "updateBest"
  /\ LET curChar == inputString[(loop % length)]
         candChar == inputString[(bestOffset + loop) % length]
     IN
       /\ curChar < candChar
       /\ bestOffset' = loop % length
  /\ pc' = "followChain"
  /\ UNCHANGED <<inputString, length, failure, matchIdx, loop>>

FollowChain ==
  /\ pc = "followChain"
  /\ matchIdx' = failure[matchIdx]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, length, failure, loop, bestOffset>>

\* After the inner loop exits, reset or extend the failure function.
PostCompare ==
  /\ pc = "postCompare"
  /\ LET curChar == inputString[(loop % length)]
         candChar == inputString[(bestOffset + loop) % length]
         newEntry == IF curChar = candChar
                       THEN IF matchIdx = Sentinel THEN 0 ELSE matchIdx + 1
                       ELSE Sentinel
         newBest == IF curChar < candChar THEN loop % length ELSE bestOffset
     IN
       /\ failure' = [failure EXCEPT ![loop - 1] = newEntry]
       /\ bestOffset' = newBest
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, length, matchIdx, loop>>

Increment ==
  /\ pc = "increment"
  /\ loop' = loop + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<inputString, length, failure, matchIdx, bestOffset>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerLoop
  \/ UpdateBest
  \/ FollowChain
  \/ PostCompare
  \/ Increment
  \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Lookup)
        /\ WF_vars(InnerLoop) /\ WF_vars(UpdateBest) /\ WF_vars(FollowChain)
        /\ WF_vars(PostCompare) /\ WF_vars(Increment)

\* Correctness: the best rotation is lexicographically minimal, and among
\* equal rotations it has the smallest shift value.
Correctness ==
  /\ \A i \in 0..(length - 1) :
       inputString[(bestOffset + i) % length] <= inputString[i]
  /\ \A i \in 0..(length - 1) :
       (inputString[(bestOffset + i) % length] = inputString[i])
         => (bestOffset <= i)

Termination == <>(pc = "done")

====