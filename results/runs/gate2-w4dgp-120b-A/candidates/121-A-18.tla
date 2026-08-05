---- MODULE LeastCircularSubstring ----
EXTENDS Naturals
CONSTANTS CharacterSet

VARIABLES inputString, strLen, failure, patIdx, loopCtr, bestOff, pc
vars == <<inputString, strLen, failure, patIdx, loopCtr, bestOff, pc>>


Seqs == CHOOSE S \in { S \in SUBSET (Char^Nat) : \A k \in Nat : k \in S => k \in Nat } : TRUE
Sentinel == 0 - 1
MaxLen == 3
Indices == {0, 1, 2}

InitStr == CHOOSE s \in Seqs : \E k \in Nat, k <= 3 : s = { m \in Nat : m < k : (m % 3) + 1 }

Init ==
  /\ inputString = InitStr
  /\ strLen = Cardinality(InitStr)
  /\ failure = [i \in (Indices \cup {0}) \cup ((Indices \cup {0}) \plus 1) |-> Sentinel]
  /\ patIdx = Sentinel
  /\ loopCtr = 1
  /\ bestOff = 0
  /\ pc = "outerLoop"

OuterLoop ==
  /\ loopCtr < 2 * strLen
  /\ pc' = "failLookup"
  /\ UNCHANGED <<inputString, strLen, failure, patIdx, loopCtr, bestOff>>

FailLookup ==
  /\ pc = "failLookup"
  /\ patIdx' = failure[(loopCtr % strLen) + bestOff]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, strLen, failure, loopCtr, bestOff>>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ \/ inputString[(loopCtr % strLen) + 1] # inputString[(patIdx % strLen) + 1]
     \/ patIdx = Sentinel
  /\ \/ inputString[(loopCtr % strLen) + 1] < inputString[(patIdx % strLen) + 1]
     /\ bestOff' = loopCtr
     /\ UNCHANGED <<inputString, strLen, failure>>
  /\ \/ inputString[(loopCtr % strLen) + 1] # inputString[(patIdx % strLen) + 1]
     /\ patIdx # Sentinel
     /\ patIdx' = failure[patIdx]
     /\ UNCHANGED <<inputString, strLen, failure, bestOff>>
  /\ \/ inputString[(loopCtr % strLen) + 1] = inputString[(patIdx % strLen) + 1]
     /\ pc' = "postComp"
     /\ UNCHANGED <<inputString, strLen, failure, patIdx, bestOff>>

PostComp ==
  /\ pc = "postComp"
  /\ \/ inputString[(loopCtr % strLen) + 1] # inputString[(patIdx % strLen) + 1]
     /\ patIdx = Sentinel
     /\ \/ inputString[(loopCtr % strLen) + 1] < inputString[(patIdx % strLen) + 1]
        /\ bestOff' = loopCtr
        /\ UNCHANGED <<inputString, strLen>>
     /\ failure' = [failure EXCEPT ![(loopCtr % strLen) + bestOff] = Sentinel]
  /\ \/ inputString[(loopCtr % strLen) + 1] = inputString[(patIdx % strLen) + 1]
     /\ failure' = [failure EXCEPT ![(loopCtr % strLen) + bestOff] = patIdx + 1]
  /\ loopCtr' = loopCtr + 1
  /\ pc' = "outerLoop"

Stall ==
  /\ pc = "outerLoop"
  /\ loopCtr >= 2 * strLen
  /\ UNCHANGED vars

Next == OuterLoop \/ FailLookup \/ InnerLoop \/ PostComp \/ Stall

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ inputString \in Seqs
  /\ strLen = Cardinality(inputString)
  /\ failure \in [((Indices \cup {0}) \cup ((Indices \cup {0}) \plus 1)) -> (Indices \cup {0} \cup {Sentinel})]
  /\ patIdx \in (Indices \cup {0} \cup {Sentinel})
  /\ loopCtr \in 0..(2 * strLen)
  /\ bestOff \in Indices
  /\ pc \in {"outerLoop", "failLookup", "innerLoop", "postComp"}

Termination == <>(pc = "outerLoop" /\ loopCtr >= 2 * strLen)

SpecProperties == Spec /\ Termination

Correctness ==
  /\ pc = "outerLoop" /\ loopCtr >= 2 * strLen => \A i \in Indices :
       inputString[(i % strLen) + 1] >= inputString[(bestOff % strLen) + 1]
  /\ pc = "outerLoop" /\ loopCtr >= 2 * strLen => \A i \in Indices :
       inputString[(i % strLen) + 1] = inputString[(bestOff % strLen) + 1] => i >= bestOff

====