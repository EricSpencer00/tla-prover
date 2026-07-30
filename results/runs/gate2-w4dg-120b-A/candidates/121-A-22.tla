---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet, Nat

Last == 99
Undefined == 99

VARIABLES inputString, length, failure, pmt, loopCnt, bestOffset, pc
vars == <<inputString, length, failure, pmt, loopCnt, bestOffset, pc>>

\* The corpus: every zero-indexed sequence built from characters in the set.
Corpus == { s \in Seq(CharacterSet) : Len(s) > 0 /\ Len(s) <= Nat }

Init ==
    /\ inputString \in Corpus
    /\ length = Len(inputString)
    /\ failure = [i \in 0..(2 * Nat) |-> Undefined]
    /\ pmt = Undefined
    /\ loopCnt = 1
    /\ bestOffset = 0
    /\ pc = "outerCheck"

OuterCheck ==
    /\ pc = "outerCheck"
    /\ IF loopCnt < 2 * length
       THEN pc' = "failureLookup"
       ELSE pc' = "done"
    /\ UNCHANGED <<inputString, length, failure, pmt, loopCnt, bestOffset>>

FailureLookup ==
    /\ pc = "failureLookup"
    /\ failure' = [failure EXCEPT ![loopCnt + bestOffset] = failure[loopCnt + bestOffset]]
    /\ pc' = "innerCompare"
    /\ UNCHANGED <<inputString, length, pmt, loopCnt, bestOffset>>

\* loopCnt and bestOffset are indices on the doubled string; the Mod operator
\* wraps them onto the base string, handling the circular nature.
Mod(i) == i % length

InnerCompare ==
    /\ pc = "innerCompare"
    /\ IF inputString[Mod(loopCnt)] # inputString[Mod(bestOffset + pmt)]
       THEN IF pmt # Undefined
            THEN pc' = "followFailure"
            ELSE pc' = "postCompare"
       ELSE pc' = "postCompare"
    /\ UNCHANGED <<inputString, length, failure, pmt, loopCnt, bestOffset>>

UpdateOffset ==
    /\ inputString[Mod(loopCnt)] < inputString[Mod(bestOffset + pmt)]
    /\ bestOffset' = loopCnt
    /\ UNCHANGED <<inputString, length, failure, pmt, loopCnt, pc>>

FollowFailure ==
    /\ pc = "followFailure"
    /\ pmt' = failure[loopCnt + bestOffset]
    /\ pc' = "innerCompare"
    /\ UNCHANGED <<inputString, length, failure, loopCnt, bestOffset>>

PostCompare ==
    /\ pc = "postCompare"
    /\ IF inputString[Mod(loopCnt)] # inputString[Mod(bestOffset + pmt)]
       THEN IF pmt = Undefined
            THEN
                /\ IF inputString[Mod(loopCnt)] < inputString[Mod(bestOffset + pmt)]
                   THEN bestOffset' = loopCnt
                   ELSE bestOffset' = bestOffset
                /\ failure' = [failure EXCEPT ![loopCnt + bestOffset] = Undefined]
            ELSE
                /\ failure' = [failure EXCEPT ![loopCnt + bestOffset] = pmt + 1]
       ELSE UNCHANGED <<failure, bestOffset>>
    /\ pc' = "increment"
    /\ UNCHANGED <<inputString, length, pmt, loopCnt>>

Increment ==
    /\ pc = "increment"
    /\ loopCnt' = loopCnt + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<inputString, length, failure, pmt, bestOffset>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == OuterCheck \/ FailureLookup \/ InnerCompare \/ UpdateOffset \/ FollowFailure \/ PostCompare \/ Increment \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Increment)

\* Type invariant: every variable stays inside its declared range.
TypeInvariant ==
    /\ inputString \in Corpus
    /\ length = Len(inputString)
    /\ failure \in [0..(2 * Nat) -> 0..Nat \cup {Undefined}]
    /\ pmt \in 0..Nat \cup {Undefined}
    /\ loopCnt \in 0..(2 * Nat)
    /\ bestOffset \in 0..(Nat - 1)
    /\ pc \in {"outerCheck", "failureLookup", "innerCompare",
              "postCompare", "increment", "done"}

\* Correctness: the rotation at bestOffset is lexicographically minimal.
Correctness ==
    \A i \in 0..(length - 1) :
        \A k \in 1..(length - 1) :
            LET rot(a) == inputString[Mod(a + i)..Mod(a + i + length - 1)]
                rotBest == inputString[Mod(a + bestOffset)..Mod(a + bestOffset + length - 1)]
            IN (rot(i) = rotBest) => (i >= bestOffset)

Termination == <>(pc = "done")

====