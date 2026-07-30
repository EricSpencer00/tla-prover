---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS
    CharacterSet

MaxStringLength == 3
MaxAlphabetSize == 2
NoMatch == 0
Sentinel == MaxAlphabetSize + 1

ZSequences == [ZSeq -> CHARACTER]

VARIABLES
    inputString,
    stringLength,
    failure,
    matched,
    loop,
    bestOffset,
    pc

vars == <<inputString, stringLength, failure, matched, loop, bestOffset, pc>>

Corpus == { s \in ZSequences : Len(s) <= MaxStringLength /\ Len(s) >= 1 }

TypeInvariant ==
    /\ inputString \in Corpus
    /\ stringLength = Len(inputString)
    /\ failure \in [0 .. 2 * MaxStringLength -> 0 .. Sentinel]
    /\ matched \in 0 .. Sentinel
    /\ loop \in 0 .. 2 * MaxStringLength
    /\ bestOffset \in 0 .. (IF stringLength = 0 THEN 0 ELSE stringLength - 1)
    /\ pc \in {"outer", "lookup", "compare", "follow", "post", "done"}

Init ==
    /\ inputString \in Corpus
    /\ stringLength = Len(inputString)
    /\ failure = [i \in 0 .. 2 * MaxStringLength |-> Sentinel]
    /\ matched = NoMatch
    /\ loop = 1
    /\ bestOffset = 0
    /\ pc = "outer"

OuterCheck ==
    /\ pc = "outer"
    /\ IF loop < 2 * MaxStringLength THEN pc' = "lookup" ELSE pc' = "done"
    /\ UNCHANGED <<inputString, stringLength, failure, matched, loop, bestOffset>>

LookupFailure ==
    /\ pc = "lookup"
    /\ matched' = failure[loop % stringLength]
    /\ pc' = "compare"
    /\ UNCHANGED <<inputString, stringLength, failure, loop, bestOffset>>

\* The character-at operation is applied modulo the string length, which is
\* always positive in the reachable states (the corpus excludes the empty string).
CharAt(n) == inputString[(n % stringLength) + 1]

CompareStep ==
    /\ pc = "compare"
    /\ IF CharAt(loop) # CharAt(bestOffset + matched + 1)
          THEN IF matched # NoMatch THEN pc' = "compare" ELSE pc' = "post"
          ELSE pc' = "compare"
    /\ matched' = IF CharAt(loop) < CharAt(bestOffset + matched + 1)
                     THEN matched + loop
                     ELSE matched
    /\ UNCHANGED <<inputString, stringLength, failure, loop, bestOffset>>

FollowFailure ==
    /\ pc = "compare"
    /\ matched # NoMatch
    /\ matched' = Sentinel
    /\ pc' = "follow"
    /\ UNCHANGED <<inputString, stringLength, failure, loop, bestOffset>>

PostComparison ==
    /\ pc = "post"
    /\ IF CharAt(loop) # CharAt(bestOffset + matched + 1) /\ matched = NoMatch
          /\ CharAt(loop) < CharAt(bestOffset + matched + 1)
          THEN bestOffset' = matched + loop
          ELSE bestOffset' = bestOffset
    /\ failure' = [failure EXCEPT ![loop] = IF matched = NoMatch THEN NoMatch ELSE matched + 1]
    /\ matched' = Sentinel
    /\ loop' = loop + 1
    /\ pc' = "outer"

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == OuterCheck \/ LookupFailure \/ CompareStep \/ FollowFailure \/ PostComparison \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(LookupFailure) /\ WF_vars(PostComparison)

\* The algorithm has explored every offset up to twice the string length and must
\* therefore have settled on the true lexicographically-smallest rotation.
Correctness ==
    /\ pc = "done"
    /\ \A i \in 0 .. (stringLength - 1) : CharAt(bestOffset) <= CharAt(i)
    /\ \A i \in 0 .. (stringLength - 1) : CharAt(bestOffset) = CharAt(i) => bestOffset <= i

Termination == <>(pc = "done")

====