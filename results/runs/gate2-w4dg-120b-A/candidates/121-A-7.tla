---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences

CONSTANTS CharacterSet, Nat

Sentinel == -1

VARIABLES inputString, strLen, failFunc, patMatch, loopCtr, bestOfs, pc

vars == <<inputString, strLen, failFunc, patMatch, loopCtr, bestOfs, pc>>

Init ==
  /\ inputString \in UNION {[1..n -> CharacterSet] : n \in Nat}
  /\ strLen = Len(inputString)
  /\ failFunc = [j \in 0..(2 * strLen) |-> Sentinel]
  /\ patMatch = Sentinel
  /\ loopCtr = 1
  /\ bestOfs = 0
  /\ pc = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF loopCtr < 2 * strLen
     THEN pc' = "compare"
     ELSE pc' = "done"
  /\ UNCHANGED <<inputString, strLen, failFunc, patMatch, loopCtr, bestOfs>>

Compare ==
  /\ pc = "compare"
  /\ patMatch' = failFunc[(loopCtr - 1) % strLen + bestOfs]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, strLen, failFunc, loopCtr, bestOfs>>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ IF inputString[(loopCtr % strLen) + 1] # inputString[(loopCtr % strLen + patMatch % strLen) + 1]
        /\ patMatch # Sentinel
     THEN pc' = "innerLoop"
     ELSE pc' = "postCompare"
  /\ IF inputString[(loopCtr % strLen) + 1] < inputString[(loopCtr % strLen + patMatch % strLen) + 1]
        /\ patMatch # Sentinel
     THEN bestOfs' = loopCtr % strLen
     ELSE bestOfs' = bestOfs
  /\ UNCHANGED <<inputString, strLen, failFunc, patMatch, loopCtr>>

Follow ==
  /\ pc = "follow"
  /\ patMatch' = failFunc[patMatch]
  /\ pc' = "postCompare"
  /\ UNCHANGED <<inputString, strLen, failFunc, loopCtr, bestOfs>>

PostCompare ==
  /\ pc = "postCompare"
  /\ IF inputString[(loopCtr % strLen) + 1] # inputString[(loopCtr % strLen + patMatch % strLen) + 1]
        /\ patMatch = Sentinel
     THEN IF inputString[(loopCtr % strLen) + 1] < inputString[(loopCtr % strLen + patMatch % strLen) + 1]
              THEN bestOfs' = loopCtr % strLen
              ELSE bestOfs' = bestOfs
          /\ failFunc' = [failFunc EXCEPT ![loopCtr] = Sentinel]
     ELSE failFunc' = [failFunc EXCEPT ![loopCtr] = patMatch + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, strLen, patMatch, loopCtr>>

Increment ==
  /\ pc = "increment"
  /\ loopCtr' = loopCtr + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<inputString, strLen, failFunc, patMatch, bestOfs>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ Compare
  \/ InnerLoop
  \/ Follow
  \/ PostCompare
  \/ Increment
  \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck)

TypeInvariant ==
  /\ inputString \in UNION {[1..n -> CharacterSet] : n \in Nat}
  /\ strLen = Len(inputString)
  /\ failFunc \in [0..(2 * strLen) -> Nat \cup {Sentinel}]
  /\ patMatch \in Nat \cup {Sentinel}
  /\ loopCtr \in 1..(2 * strLen)
  /\ bestOfs \in 0..(strLen - 1)
  /\ pc \in {"outerCheck", "compare", "innerLoop", "follow", "postCompare", "increment", "done"}

Correctness ==
  /\ pc = "done"
  /\ \A i \in 0..(strLen - 1) : inputString[bestOfs + 1 .. strLen] ^ inputString[1 .. bestOfs]
                            <= inputString[(i + 1) .. strLen] ^ inputString[1 .. i]
  /\ \A i \in 0..(strLen - 1) :
       (inputString[bestOfs + 1 .. strLen] ^ inputString[1 .. bestOfs]
        = inputString[(i + 1) .. strLen] ^ inputString[1 .. i])
         => bestOfs <= i

Termination == <>(pc = "done")

====