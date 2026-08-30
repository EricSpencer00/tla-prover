---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

(* The Booth least-circular-substring algorithm runs as a single linear walk  *)
(* over a doubled string; the failure function is a KMP-style backtrack chain. *)
(* The character set is a finite NUMERIC subset of Nat, overridden here as a   *)
(* bounded version of Nat so the model is finite.                             *)

CONSTANTS CharacterSet

VARIABLES inputString, stringLength, failFunc, patternIdx, loopCnt, bestOffset, pc

vars == <<inputString, stringLength, failFunc, patternIdx, loopCnt, bestOffset, pc>>

Sentinel == 999
MaxLen == 2
MaxLoop == 4

TypeInvariant ==
    /\ inputString \in [1..MaxLen -> CharacterSet]
    /\ stringLength \in 0..MaxLen
    /\ failFunc \in [0..(MaxLen * 2) -> (0..(MaxLen * 2)) \cup {Sentinel}]
    /\ patternIdx \in (0..(MaxLen * 2)) \cup {Sentinel}
    /\ loopCnt \in 1..MaxLoop
    /\ bestOffset \in 0..(MaxLen - 1)
    /\ pc \in {"outer", "lookup", "compare", "updateAfterLoop", "follow",
               "post", "term"}

Init ==
    /\ \E s \in [1..MaxLen -> CharacterSet] :
        /\ inputString = s
        /\ stringLength = Len(s)
    /\ failFunc = [i \in 0..(MaxLen * 2) |-> Sentinel]
    /\ patternIdx = Sentinel
    /\ loopCnt = 1
    /\ bestOffset = 0
    /\ pc = "outer"

OuterLoop ==
    /\ pc = "outer"
    /\ IF loopCnt < MaxLoop
       THEN /\ pc' = "lookup"
            /\ UNCHANGED <<inputString, stringLength, failFunc, patternIdx, loopCnt, bestOffset>>
       ELSE /\ pc' = "term"
            /\ UNCHANGED <<inputString, stringLength, failFunc, patternIdx, loopCnt, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ patternIdx' = failFunc[loopCnt - 1]
    /\ pc' = "compare"
    /\ UNCHANGED <<inputString, stringLength, failFunc, loopCnt, bestOffset>>

\* The inner loop walks forwards along the doubled string, comparing chars.
Compare ==
    /\ pc = "compare"
    /\ LET i == loopCnt % stringLength
           j == (bestOffset + loopCnt) % stringLength
       IN /\ inputString[i] # inputString[j]
          /\ \/ patternIdx # Sentinel
             \/ pc' = "post"
          /\ IF patternIdx # Sentinel
             THEN pc' \in {"post", "compare"}
             ELSE pc' = "post"
    /\ UNCHANGED <<inputString, stringLength, failFunc, patternIdx, loopCnt, bestOffset>>

UpdateAfterLoop ==
    /\ pc = "updateAfterLoop"
    /\ LET i == loopCnt % stringLength
           j == (bestOffset + loopCnt) % stringLength
       IN /\ inputString[i] < inputString[j]
          /\ bestOffset' = loopCnt
    /\ pc' = "follow"
    /\ UNCHANGED <<inputString, stringLength, failFunc, patternIdx, loopCnt>>

Follow ==
    /\ pc = "follow"
    /\ patternIdx' = IF patternIdx = Sentinel THEN Sentinel ELSE failFunc[patternIdx]
    /\ pc' = "post"
    /\ UNCHANGED <<inputString, stringLength, failFunc, loopCnt, bestOffset>>

Post ==
    /\ pc = "post"
    /\ LET i == loopCnt % stringLength
           j == (bestOffset + loopCnt) % stringLength
       IN /\ IF inputString[i] # inputString[j] /\ patternIdx = Sentinel
             /\ inputString[i] < inputString[j]
             THEN bestOffset' = loopCnt
             ELSE bestOffset' = bestOffset
          /\ failFunc' = [failFunc EXCEPT
                           ![loopCnt] = IF patternIdx = Sentinel
                                          THEN Sentinel
                                          ELSE patternIdx + 1]
    /\ pc' = "increment"
    /\ UNCHANGED <<inputString, stringLength, patternIdx, loopCnt>>

Increment ==
    /\ pc = "increment"
    /\ loopCnt' = loopCnt + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<inputString, stringLength, failFunc, patternIdx, bestOffset>>

\* Stutter once the algorithm has finished.
Stutter ==
    /\ pc = "term"
    /\ UNCHANGED vars

Next == OuterLoop \/ Lookup \/ Compare \/ UpdateAfterLoop \/ Follow \/ Post
        \/ Increment \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(Increment)

\* Correctness: the rotation at bestOffset is the lexicographically smallest.
Correctness ==
    /\ \A k \in 1..(stringLength - 1) :
         LET a == [i \in 1..stringLength |-> inputString[(bestOffset + i) % stringLength]]
             b == [i \in 1..stringLength |-> inputString[(bestOffset + k + i) % stringLength]]
         IN a <= b
    /\ \A k \in 1..(stringLength - 1) :
         LET a == [i \in 1..stringLength |-> inputString[(bestOffset + i) % stringLength]]
             b == [i \in 1..stringLength |-> inputString[(bestOffset + k + i) % stringLength]]
         IN (a = b) => (bestOffset <= (bestOffset + k) % stringLength)

Termination == <>(pc = "term")

====