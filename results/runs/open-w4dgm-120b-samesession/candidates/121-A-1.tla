---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CharacterSet

Sentinel == 0
MaxLength == 2
Characters == {1, 2, 3}

VARIABLES string, length, failure, patternIndex, loopCounter, bestOffset, pc

vars == <<string, length, failure, patternIndex, loopCounter, bestOffset, pc>>

InCorpus(s) == s \in [1..MaxLength -> Characters]

TypeInvariant ==
    /\ InCorpus(string)
    /\ length = Len(string)
    /\ failure \in [0..(2 * MaxLength)] -> (0..(2 * MaxLength))
    /\ patternIndex \in 0..(2 * MaxLength)
    /\ loopCounter \in 0..(2 * MaxLength)
    /\ bestOffset \in 0..(MaxLength - 1)
    /\ pc \in {"outerCheck", "lookup", "innerLoop", "updateOffset", "followChain", "postCompare", "terminating"}

Init ==
    /\ \E s \in [1..MaxLength -> Characters] : string = s
    /\ length = Len(string)
    /\ failure = [i \in 0..(2 * MaxLength) |-> Sentinel]
    /\ patternIndex = Sentinel
    /\ loopCounter = 1
    /\ bestOffset = 0
    /\ pc = "outerCheck"

OuterLoopCheck ==
    /\ pc = "outerCheck"
    /\ IF loopCounter < (2 * length)
       THEN pc' = "lookup"
       ELSE pc' = "terminating"
    /\ UNCHANGED <<string, length, failure, patternIndex, loopCounter, bestOffset>>

LookupFailure ==
    /\ pc = "lookup"
    /\ failure \in [0..(2 * MaxLength) -> (0..(2 * MaxLength))]
    /\ patternIndex' = failure[loopCounter % length]
    /\ pc' = "innerLoop"
    /\ UNCHANGED <<string, length, failure, loopCounter, bestOffset>>

InnerLoopCompare ==
    /\ pc = "innerLoop"
    /\ LET candPos == (loopCounter - bestOffset) % length
           curChar == string[(loopCounter % length) + 1]
           candChar == string[candPos + 1]
       IN /\ IF curChar # candChar /\ patternIndex # Sentinel
              THEN pc' = "innerLoop"
              ELSE pc' = "postCompare"
    /\ UNCHANGED <<string, length, failure, patternIndex, loopCounter, bestOffset>>

UpdateOffset ==
    /\ pc = "postCompare"
    /\ LET candPos == (loopCounter - bestOffset) % length
           curChar == string[(loopCounter % length) + 1]
           candChar == string[candPos + 1]
       IN IF curChar < candChar
            THEN bestOffset' = loopCounter
            ELSE bestOffset' = bestOffset
    /\ UNCHANGED <<string, length, failure, patternIndex, loopCounter, pc>>

FollowChain ==
    /\ pc = "postCompare"
    /\ LET candPos == (loopCounter - bestOffset) % length
           curChar == string[(loopCounter % length) + 1]
           candChar == string[candPos + 1]
           nextPattern == IF curChar # candChar /\ patternIndex = Sentinel
                            THEN Sentinel
                            ELSE IF curChar # candChar
                                   THEN failure[loopCounter]
                                   ELSE patternIndex + 1
       IN /\ patternIndex' = nextPattern
          /\ failure' = [failure EXCEPT ![loopCounter] = nextPattern]
    /\ loopCounter' = loopCounter + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<string, length, bestOffset>>

Stall ==
    /\ pc = "terminating"
    /\ UNCHANGED vars

Next ==
    \/ OuterLoopCheck
    \/ LookupFailure
    \/ InnerLoopCompare
    \/ UpdateOffset
    \/ FollowChain
    \/ Stall

Spec == Init /\ [][Next]_vars

Correctness ==
    /\ LET rotatedAt(k) ==
            [i \in 1..length |-> string[((i + k - 1) % length) + 1]]
       IN \A k \in 0..(length - 1) :
            /\ rotatedAt(bestOffset) <= rotatedAt(k)
            /\ (rotatedAt(bestOffset) = rotatedAt(k) => bestOffset <= k)

Termination == <>(pc = "terminating")

====