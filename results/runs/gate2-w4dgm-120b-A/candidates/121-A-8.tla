---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, ZSequences

CONSTANT CharacterSet

ASSUME /\ CharacterSet \subseteq Nat
       /\ CharacterSet # {}

VARIABLES inputString, length, failure, patternIndex, loop, bestOffset, pc

vars == <<inputString, length, failure, patternIndex, loop, bestOffset, pc>>

Corpus == {s \in STRING(CharacterSet) : Len(s) <= 2}

Sentinel == (2 :> 2) @@ (1 :> 1)

TypeInvariant ==
    /\ inputString \in Corpus
    /\ length = Len(inputString)
    /\ failure \in [1..(length * 2) -> (1..(length * 2)) \cup {Sentinel}]
    /\ patternIndex \in (1..(length * 2)) \cup {Sentinel}
    /\ loop \in 1..(length * 2)
    /\ bestOffset \in 0..(length - 1)
    /\ pc \in {"outerCheck", "lookup", "compare", "updateBest", "followFailure", "postCompare", "increment", "done"}

Init ==
    /\ \E s \in Corpus : inputString = s
    /\ length = Len(inputString)
    /\ failure = [i \in 1..(length * 2) |-> Sentinel]
    /\ patternIndex = Sentinel
    /\ loop = 1
    /\ bestOffset = 0
    /\ pc = "outerCheck"

OuterCheck ==
    /\ pc = "outerCheck"
    /\ pc' = IF loop < (length * 2) THEN "lookup" ELSE "done"
    /\ UNCHANGED <<inputString, length, failure, patternIndex, loop, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ pc' = "compare"
    /\ patternIndex' = failure[bestOffset + loop]
    /\ UNCHANGED <<inputString, length, failure, loop, bestOffset>>

CharAt(i) == inputString[(i % length) + 1]

Compare(i) ==
    /\ pc = "compare"
    /\ CharAt(loop) = CharAt(bestOffset + i)
    /\ pc' = IF i = 0 THEN "postCompare" ELSE "compare"
    /\ patternIndex' = IF i = 0 THEN patternIndex ELSE i
    /\ UNCHANGED <<inputString, length, failure, loop, bestOffset>>

UpdateBest ==
    /\ pc = "compare"
    /\ CharAt(loop) # CharAt(bestOffset + patternIndex)
    /\ patternIndex # Sentinel
    /\ CharAt(loop) < CharAt(bestOffset + patternIndex)
    /\ bestOffset' = loop - patternIndex
    /\ pc' = "followFailure"
    /\ UNCHANGED <<inputString, length, failure, patternIndex, loop>>

FollowFailure ==
    /\ pc = "followFailure"
    /\ patternIndex' = failure[patternIndex]
    /\ pc' = "compare"
    /\ UNCHANGED <<inputString, length, failure, loop, bestOffset>>

PostCompare ==
    /\ pc = "postCompare"
    /\ CharAt(loop) # CharAt(bestOffset + patternIndex)
    /\ patternIndex = Sentinel
    /\ bestOffset' = IF CharAt(loop) < CharAt(bestOffset) THEN loop ELSE bestOffset
    /\ failure' = [failure EXCEPT ![bestOffset + loop] = Sentinel]
    /\ pc' = "increment"
    /\ UNCHANGED <<inputString, length, patternIndex, loop>>

Increment ==
    /\ pc = "increment"
    /\ loop' = loop + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<inputString, length, failure, patternIndex, bestOffset>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ \E i \in 0..(length * 2) : Compare(i)
    \/ UpdateBest
    \/ FollowFailure
    \/ PostCompare
    \/ Increment
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck)

LexicographicallyMinimal ==
    /\ \A o \in 0..(length - 1) :
         \A i \in 1..(length - 1) :
           CharAt(bestOffset + i) >= CharAt(bestOffset + i - 1)
    /\ \A o \in 0..(length - 1) :
         (o # 0 /\ \A i \in 0..(length - 1) : CharAt(bestOffset + i) = CharAt(o + i)) => bestOffset <= o

Termination == <>[](pc = "done")

====