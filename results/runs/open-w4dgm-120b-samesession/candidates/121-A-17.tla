---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

Sentinel == 99

VARIABLES inputString, strLen, failFunc, patIdx, loopVar, bestOffset, pc

vars == <<inputString, strLen, failFunc, patIdx, loopVar, bestOffset, pc>>

Corpus == UNION {[1..n -> CharacterSet] : n \in Nat}

TypeInvariant ==
    /\ inputString \in Corpus
    /\ strLen = Len(inputString)
    /\ failFunc \in [0..(2 * strLen) -> (0..strLen) \cup {Sentinel}]
    /\ patIdx \in 0..strLen \cup {Sentinel}
    /\ loopVar \in 0..(2 * strLen)
    /\ bestOffset \in 0..(strLen - 1)
    /\ pc \in {"outer", "lookup", "inner", "post", "done"}

Init ==
    /\ inputString \in Corpus
    /\ strLen = Len(inputString)
    /\ failFunc = [k \in 0..(2 * strLen) |-> Sentinel]
    /\ patIdx = Sentinel
    /\ loopVar = 1
    /\ bestOffset = 0
    /\ pc = "outer"

OuterLoop ==
    /\ pc = "outer"
    /\ loopVar < 2 * strLen
    /\ pc' = "lookup"
    /\ UNCHANGED <<inputString, strLen, failFunc, patIdx, loopVar, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ failFunc' = [failFunc EXCEPT ![loopVar] = failFunc[loopVar - 1]]
    /\ patIdx' = failFunc[loopVar]
    /\ pc' = "inner"
    /\ UNCHANGED <<inputString, strLen, loopVar, bestOffset>>

InnerLoop ==
    /\ pc = "inner"
    /\ inputString[(loopVar % strLen) + 1] # inputString[((bestOffset + loopVar) % strLen) + 1]
    /\ patIdx # Sentinel
    /\ pc' = "inner"
    /\ UNCHANGED <<inputString, strLen, failFunc, patIdx, loopVar, bestOffset>>

UpdateOnLess ==
    /\ pc \in {"inner", "post"}
    /\ inputString[(loopVar % strLen) + 1] < inputString[((bestOffset + loopVar) % strLen) + 1]
    /\ bestOffset' = (bestOffset + loopVar) % strLen
    /\ UNCHANGED <<inputString, strLen, failFunc, patIdx, loopVar, pc>>

FollowFailure ==
    /\ pc = "inner"
    /\ inputString[(loopVar % strLen) + 1] # inputString[((bestOffset + loopVar) % strLen) + 1]
    /\ patIdx # Sentinel
    /\ patIdx' = failFunc[patIdx]
    /\ pc' = "inner"
    /\ UNCHANGED <<inputString, strLen, failFunc, loopVar, bestOffset>>

PostComparison ==
    /\ pc = "inner"
    /\ inputString[(loopVar % strLen) + 1] # inputString[((bestOffset + loopVar) % strLen) + 1]
    /\ patIdx = Sentinel
    /\ pc' = "post"
    /\ UNCHANGED <<inputString, strLen, failFunc, patIdx, loopVar, bestOffset>>

ResetFailFunc ==
    /\ pc = "post"
    /\ inputString[(loopVar % strLen) + 1] # inputString[((bestOffset + loopVar) % strLen) + 1]
    /\ failFunc' = [failFunc EXCEPT ![loopVar] = Sentinel]
    /\ pc' = "post"
    /\ UNCHANGED <<inputString, strLen, patIdx, loopVar, bestOffset>>

ExtendFailFunc ==
    /\ pc = "post"
    /\ inputString[(loopVar % strLen) + 1] = inputString[((bestOffset + loopVar) % strLen) + 1]
    /\ failFunc' = [failFunc EXCEPT ![loopVar] = IF patIdx = Sentinel THEN 1 ELSE patIdx + 1]
    /\ pc' = "post"
    /\ UNCHANGED <<inputString, strLen, patIdx, loopVar, bestOffset>>

NextLoop ==
    /\ pc = "post"
    /\ loopVar' = loopVar + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<inputString, strLen, failFunc, patIdx, bestOffset>>

Terminate ==
    /\ pc = "outer"
    /\ loopVar >= 2 * strLen
    /\ pc' = "done"
    /\ UNCHANGED <<inputString, strLen, failFunc, patIdx, loopVar, bestOffset>>

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ OuterLoop
    \/ Lookup
    \/ InnerLoop
    \/ UpdateOnLess
    \/ FollowFailure
    \/ PostComparison
    \/ ResetFailFunc
    \/ ExtendFailFunc
    \/ NextLoop
    \/ Terminate
    \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop)

\* Lexicographic minimality of the rotation at bestOffset, with a strict
\* tie-breaker on the shift value when two rotations are equal.
Correctness ==
    /\ \A i \in 0..(strLen - 1) : \A j \in 0..(strLen - 1) :
        (LexSeq(i) # LexSeq(j) => LexSeq(i) \prec LexSeq(j))
        /\ (LexSeq(i) = LexSeq(j) => i <= j)
    /\ pc = "done"
    /\ loopVar >= 2 * strLen
    /\ strLen > 0

LexSeq(i) == << inputString[((i + k) % strLen) + 1] : k \in 0..(strLen - 1) >>

Termination == <>(pc = "done")
====