---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences
CONSTANTS CharacterSet

Sentinel == 999
Corpus == UNION { [1 .. n -> 1 .. CharacterSet] : n \in Nat }

VARIABLES inputStr, strLen, fail, matchIdx, loopCtr, bestOffset, pc
vars == << inputStr, strLen, fail, matchIdx, loopCtr, bestOffset, pc >>

TypeInvariant ==
    /\ inputStr \in Corpus
    /\ strLen = Len(inputStr)
    /\ fail \in [0 .. 2 * strLen -> 0 .. 2 * strLen \cup {Sentinel}]
    /\ matchIdx \in 0 .. 2 * strLen \cup {Sentinel}
    /\ loopCtr \in 1 .. 2 * strLen
    /\ bestOffset \in 0 .. (strLen - 1)
    /\ pc \in {"outerCheck", "lookup", "innerLoop", "update", "followFail", "postCompare", "done"}

Init ==
    /\ inputStr \in Corpus
    /\ strLen = Len(inputStr)
    /\ fail = [i \in 0 .. 2 * strLen |-> Sentinel]
    /\ matchIdx = Sentinel
    /\ loopCtr = 1
    /\ bestOffset = 0
    /\ pc = "outerCheck"

OuterCheck ==
    /\ pc = "outerCheck"
    /\ pc' = IF loopCtr < 2 * strLen THEN "lookup" ELSE "done"
    /\ UNCHANGED << inputStr, strLen, fail, matchIdx, loopCtr, bestOffset >>

Lookup ==
    /\ pc = "lookup"
    /\ matchIdx' = fail[loopCtr - bestOffset]
    /\ pc' = "innerLoop"
    /\ UNCHANGED << inputStr, strLen, fail, loopCtr, bestOffset >>

InnerLoop ==
    /\ pc = "innerLoop"
    /\ IF inputStr[(loopCtr % strLen) + 1] # inputStr[((bestOffset + loopCtr) % strLen) + 1]
       THEN IF matchIdx # Sentinel THEN pc' = "followFail" ELSE pc' = "postCompare"
       ELSE pc' = "postCompare"
    /\ UNCHANGED << inputStr, strLen, fail, matchIdx, loopCtr, bestOffset >>

Update ==
    /\ pc = "update"
    /\ inputStr[(loopCtr % strLen) + 1] < inputStr[((bestOffset + loopCtr) % strLen) + 1]
    /\ bestOffset' = (bestOffset + loopCtr) % strLen
    /\ pc' = "postCompare"
    /\ UNCHANGED << inputStr, strLen, fail, matchIdx, loopCtr >>

FollowFail ==
    /\ pc = "followFail"
    /\ matchIdx' = IF matchIdx = Sentinel THEN Sentinel ELSE fail[matchIdx]
    /\ pc' = "innerLoop"
    /\ UNCHANGED << inputStr, strLen, fail, loopCtr, bestOffset >>

PostCompare ==
    /\ pc = "postCompare"
    /\ IF inputStr[(loopCtr % strLen) + 1] # inputStr[((bestOffset + loopCtr) % strLen) + 1]
          /\ matchIdx = Sentinel
          /\ inputStr[(loopCtr % strLen) + 1] < inputStr[((bestOffset + loopCtr) % strLen) + 1]
       THEN bestOffset' = (bestOffset + loopCtr) % strLen
       ELSE bestOffset' = bestOffset
    /\ fail' = [fail EXCEPT ![loopCtr - bestOffset] =
                  IF inputStr[(loopCtr % strLen) + 1] = inputStr[((bestOffset + loopCtr) % strLen) + 1]
                  THEN matchIdx + 1 ELSE Sentinel]
    /\ loopCtr' = loopCtr + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED << inputStr, strLen, matchIdx >>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck \/ Lookup \/ InnerLoop \/ Update \/ FollowFail \/ PostCompare \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(PostCompare)

Correctness ==
    /\ (\A k \in 1 .. (strLen - 1) : inputStr[(bestOffset + 1) .. (bestOffset + k)]
           <= inputStr[1 .. k])
    /\ (\A k \in 1 .. (strLen - 1) :
           inputStr[(bestOffset + 1) .. (bestOffset + k)] = inputStr[1 .. k]
             => bestOffset <= k)

Termination == <>(pc = "done")
====