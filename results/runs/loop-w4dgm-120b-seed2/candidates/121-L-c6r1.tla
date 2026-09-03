---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS CharacterSet
VARIABLES inputString, strLen, fail, matchIdx, loopIdx, bestOffset, pc
vars == <<inputString, strLen, fail, matchIdx, loopIdx, bestOffset, pc>>
Sentinel == 99
MaxLen == 2
Types ==
    /\ inputString \in [1..MaxLen -> CharacterSet]
    /\ strLen \in 1..MaxLen
    /\ fail \in [1..(2 * MaxLen) -> (0..MaxLen) \cup {Sentinel}]
    /\ matchIdx \in (0..MaxLen) \cup {Sentinel}
    /\ loopIdx \in 1..(2 * MaxLen)
    /\ bestOffset \in 0..(MaxLen - 1)
    /\ pc \in {"outerCheck", "failLookup", "innerLoop", "updateOffset", "followChain",
                "postCompare", "increment", "done"}
Init ==
    /\ inputString \in [1..MaxLen -> CharacterSet]
    /\ strLen = Len(inputString)
    /\ fail = [i \in 1..(2 * MaxLen) |-> Sentinel]
    /\ matchIdx = Sentinel
    /\ loopIdx = 1
    /\ bestOffset = 0
    /\ pc = "outerCheck"
OuterCheck ==
    /\ pc = "outerCheck"
    /\ IF loopIdx < (2 * strLen) THEN pc' = "failLookup" ELSE pc' = "done"
    /\ UNCHANGED <<inputString, strLen, fail, matchIdx, loopIdx, bestOffset>>
FailLookup ==
    /\ pc = "failLookup"
    /\ matchIdx' = fail[loopIdx - bestOffset]
    /\ pc' = "innerLoop"
    /\ UNCHANGED <<inputString, strLen, fail, loopIdx, bestOffset>>
InnerLoop ==
    /\ pc = "innerLoop"
    /\ LET cur == inputString[(loopIdx % strLen) + 1]
           cand == inputString[((bestOffset + loopIdx) % strLen) + 1] IN
        IF cur # cand /\ matchIdx # Sentinel THEN pc' = "postCompare"
        ELSE IF cur < cand THEN pc' = "updateOffset"
        ELSE pc' = "followChain"
    /\ UNCHANGED <<inputString, strLen, fail, matchIdx, loopIdx, bestOffset>>
UpdateOffset ==
    /\ pc = "updateOffset"
    /\ LET cur == inputString[(loopIdx % strLen) + 1]
           cand == inputString[((bestOffset + loopIdx) % strLen) + 1] IN
        IF cur < cand THEN bestOffset' = loopIdx % strLen ELSE bestOffset' = bestOffset
    /\ pc' = "followChain"
    /\ UNCHANGED <<inputString, strLen, fail, matchIdx, loopIdx>>
FollowChain ==
    /\ pc = "followChain"
    /\ matchIdx' = IF matchIdx = Sentinel THEN Sentinel ELSE fail[matchIdx]
    /\ pc' = "postCompare"
    /\ UNCHANGED <<inputString, strLen, fail, loopIdx, bestOffset>>
PostCompare ==
    /\ pc = "postCompare"
    /\ LET cur == inputString[(loopIdx % strLen) + 1]
           cand == inputString[((bestOffset + loopIdx) % strLen) + 1] IN
        /\ IF cur < cand /\ matchIdx = Sentinel
           THEN bestOffset' = loopIdx % strLen
           ELSE bestOffset' = bestOffset
        /\ IF cur = cand
           THEN fail' = [fail EXCEPT ![loopIdx + 1] = IF matchIdx = Sentinel THEN Sentinel ELSE matchIdx + 1]
           ELSE fail' = [fail EXCEPT ![loopIdx + 1] = Sentinel]
    /\ pc' = "increment"
    /\ UNCHANGED <<inputString, strLen, matchIdx, loopIdx>>
Increment ==
    /\ pc = "increment"
    /\ loopIdx' = loopIdx + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<inputString, strLen, fail, matchIdx, bestOffset>>
Done ==
    /\ pc = "done"
    /\ UNCHANGED vars
Next == OuterCheck \/ FailLookup \/ InnerLoop \/ UpdateOffset \/ FollowChain \/ PostCompare \/ Increment \/ Done
Spec == Init /\ [][Next]_vars /\ WF_vars(Done)
TypeInvariant == Types
LexicographicallyMinimal ==
    /\ \A i \in 0..(strLen - 1) :
         \A j \in 0..(strLen - 1) :
            LET s(i) == <<inputString[((i + k) % strLen) + 1] : k \in 0..(strLen - 1)>>
                s(j) == <<inputString[((j + k) % strLen) + 1] : k \in 0..(strLen - 1)>>
            IN LexicographicOrder(s(bestOffset), s(i)) <= 0
    /\ \A i \in 0..(strLen - 1) :
         (LexicographicOrder(<<inputString[((bestOffset + k) % strLen) + 1] : k \in 0..(strLen - 1)>>,
                             <<inputString[((i + k) % strLen) + 1] : k \in 0..(strLen - 1)>>) = 0)
          => bestOffset <= i
Termination == <>(pc = "done")
====