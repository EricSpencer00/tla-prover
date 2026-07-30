---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

(* The alphabet is a finite, non-empty subset of the naturals.  It replaces the *)
(* unbounded Nat from Naturals, keeping the model finite.                     *)
CONSTANTS CharacterSet

(* Zero-indexed sequence of characters, ranging over the corpus.               *)
VARIABLES inputString, strLen, failure, patIdx, loopIdx, bestOffset, pc

vars == <<inputString, strLen, failure, patIdx, loopIdx, bestOffset, pc>>

(* Sentinel value meaning "undefined" in the failure function.                *)
Undefined == 99

TypeOK ==
    /\ inputString \in Seq(CharacterSet)
    /\ strLen \in Nat
    /\ failure \in [0..(2 * strLen) -> 0..(2 * strLen) \cup {Undefined}]
    /\ patIdx \in 0..(2 * strLen) \cup {Undefined}
    /\ loopIdx \in 0..(2 * strLen)
    /\ bestOffset \in 0..(strLen - 1)
    /\ pc \in {"LoopEntry", "Lookup", "Inner", "UpdateBest", "Follow",
               "PostCompare", "Increment"}

Init ==
    /\ inputString \in Seq(CharacterSet)
    /\ strLen = Len(inputString)
    /\ failure = [i \in 0..(2 * strLen) |-> Undefined]
    /\ patIdx = Undefined
    /\ loopIdx = 1
    /\ bestOffset = 0
    /\ pc = "LoopEntry"

LoopEntry ==
    /\ pc = "LoopEntry"
    /\ IF loopIdx < (2 * strLen)
       THEN pc' = "Lookup"
       ELSE pc' = "LoopEntry"
    /\ UNCHANGED <<inputString, strLen, failure, patIdx, loopIdx, bestOffset>>

Lookup ==
    /\ pc = "Lookup"
    /\ failure' = [failure EXCEPT ![loopIdx - bestOffset] = failure[loopIdx - bestOffset]]
    /\ pc' = "Inner"
    /\ UNCHANGED <<inputString, strLen, patIdx, loopIdx, bestOffset>>

Inner ==
    /\ pc = "Inner"
    /\ LET curChar == inputString[(loopIdx % strLen) + 1]
           candChar == inputString[((loopIdx - bestOffset) % strLen) + 1]
       IN IF curChar # candChar /\ patIdx # Undefined
          THEN pc' = "UpdateBest"
          ELSE pc' = "PostCompare"
    /\ UNCHANGED <<inputString, strLen, failure, patIdx, loopIdx, bestOffset>>

UpdateBest ==
    /\ pc = "UpdateBest"
    /\ LET curChar == inputString[(loopIdx % strLen) + 1]
           candChar == inputString[((loopIdx - bestOffset) % strLen) + 1]
       IN IF curChar < candChar
          THEN bestOffset' = loopIdx % strLen
          ELSE UNCHANGED bestOffset
    /\ pc' = "Follow"
    /\ UNCHANGED <<inputString, strLen, failure, patIdx, loopIdx>>

Follow ==
    /\ pc = "Follow"
    /\ patIdx' = IF patIdx = Undefined THEN Undefined ELSE failure[patIdx]
    /\ pc' = "Inner"
    /\ UNCHANGED <<inputString, strLen, failure, loopIdx, bestOffset>>

PostCompare ==
    /\ pc = "PostCompare"
    /\ LET curChar == inputString[(loopIdx % strLen) + 1]
           candChar == inputString[((loopIdx - bestOffset) % strLen) + 1]
       IN LET newBest ==
                IF curChar < candChar
                THEN loopIdx % strLen
                ELSE bestOffset
              newFailure ==
                IF curChar = candChar
                THEN IF patIdx = Undefined THEN 0 ELSE patIdx + 1
                ELSE Undefined
          IN /\ bestOffset' = newBest
             /\ failure' = [failure EXCEPT ![loopIdx - bestOffset] = newFailure]
    /\ pc' = "Increment"
    /\ UNCHANGED <<inputString, strLen, patIdx, loopIdx>>

Increment ==
    /\ pc = "Increment"
    /\ loopIdx' = loopIdx + 1
    /\ pc' = "LoopEntry"
    /\ UNCHANGED <<inputString, strLen, failure, patIdx, bestOffset>>

Stall ==
    /\ ~(pc = "LoopEntry" /\ loopIdx >= (2 * strLen))
    /\ UNCHANGED vars

Next ==
    \/ LoopEntry
    \/ Lookup
    \/ Inner
    \/ UpdateBest
    \/ Follow
    \/ PostCompare
    \/ Increment
    \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Lookup) /\ WF_vars(PostCompare)

Terminated ==
    pc = "LoopEntry" /\ loopIdx >= (2 * strLen)

Correctness ==
    /\ Terminated
    /\ \A i \in 1..(strLen - 1) :
         LET candidate == inputString[(bestOffset + i - 1) % strLen + 1]
             offsetChar == inputString[bestOffset + 1]
         IN candidate >= offsetChar
    /\ \A i \in 1..(strLen - 1) :
         (inputString[(bestOffset + i - 1) % strLen + 1]
          = inputString[bestOffset + 1]) => i >= bestOffset

Termination == <>(Terminated)

====