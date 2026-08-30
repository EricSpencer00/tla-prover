---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* Finite-cast Naturals for bounded model checking; retains full NAT ordering.
Nat == CHOOSE n \in CharacterSet : \A m \in CharacterSet : m <= n
CharacterSet == Nat

\* The algorithm treats the input as a doubled circular buffer, so the loop
\* counter ranges over twice the string length and each indexed read is
\* wrapped modulo that length. The failure function is the KMP-style back
\* pointer that gives the algorithm its linear-time guarantee.

InputString == [1..StringLen -> CharacterSet]

VARIABLES string, ffunc, patIdx, loopCnt, bestOffset, pc

vars == <<string, ffunc, patIdx, loopCnt, bestOffset, pc>>

StringLen == Len(string)
Sentinel == StringLen
MaxLoop == StringLen * 2

TypeInvariant ==
    /\ string \in InputString
    /\ ffunc \in [0..MaxLoop -> 0..StringLen]
    /\ patIdx \in 0..StringLen
    /\ loopCnt \in 0..MaxLoop
    /\ bestOffset \in 0..(StringLen - 1)
    /\ pc \in {"OuterCheck", "LookupFail", "InnerLoop", "UpdateBest",
               "FollowFailure", "PostCompare", "Done"}

\* The current character of the doubled buffer at the loop counter.
CurrentChar ==
    string[(loopCnt % StringLen) + 1]

\* The candidate character offset by the best rotation so far.
CandidateChar ==
    string[((loopCnt + bestOffset) % StringLen) + 1]

Init ==
    /\ \E s \in InputString : string = s
    /\ ffunc = [i \in 0..MaxLoop |-> Sentinel]
    /\ patIdx = Sentinel
    /\ loopCnt = 1
    /\ bestOffset = 0
    /\ pc = "OuterCheck"

OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF loopCnt < MaxLoop THEN pc' = "LookupFail" ELSE pc' = "Done"
    /\ UNCHANGED <<string, ffunc, patIdx, loopCnt, bestOffset>>

LookupFail ==
    /\ pc = "LookupFail"
    /\ patIdx' = ffunc[loopCnt - 1]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<string, ffunc, loopCnt, bestOffset>>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ IF CurrentChar # CandidateChar /\ patIdx # Sentinel
       THEN pc' = "FollowFailure" ELSE pc' = "PostCompare"
    /\ UNCHANGED <<string, ffunc, patIdx, loopCnt, bestOffset>>

UpdateBest ==
    /\ pc = "UpdateBest"
    /\ CurrentChar < CandidateChar
    /\ bestOffset' = loopCnt
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<string, ffunc, patIdx, loopCnt>>

FollowFailure ==
    /\ pc = "FollowFailure"
    /\ patIdx' = ffunc[patIdx]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<string, ffunc, loopCnt, bestOffset>>

PostCompare ==
    /\ pc = "PostCompare"
    /\ IF CurrentChar # CandidateChar /\ patIdx = Sentinel
       THEN IF CurrentChar < CandidateChar
            THEN bestOffset' = loopCnt
            ELSE bestOffset' = bestOffset
            /\ ffunc' = [ffunc EXCEPT ![loopCnt] = Sentinel]
       ELSE ffunc' = [ffunc EXCEPT ![loopCnt] = IF patIdx = Sentinel
                                                THEN Sentinel ELSE patIdx + 1]
    /\ pc' = "Advance"
    /\ UNCHANGED <<string, patIdx, loopCnt>>

Advance ==
    /\ pc = "Advance"
    /\ loopCnt' = loopCnt + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<string, ffunc, patIdx, bestOffset>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck \/ LookupFail \/ InnerLoop \/ UpdateBest
    \/ FollowFailure \/ PostCompare \/ Advance \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Done)

\* Correctness: the rotation at the best offset is lexicographically <= every
\* other rotation, and if two rotations compare equal the offset is minimal.
Correctness ==
    \A i \in 0..(StringLen - 1) :
        \/ \A k \in 0..(StringLen - 1) : string[((i + k) % StringLen) + 1] <=
                                          string[((bestOffset + k) % StringLen) + 1]
        \/ (\A k \in 0..(StringLen - 1) :
              (string[((i + k) % StringLen) + 1] = string[((bestOffset + k) % StringLen) + 1])
                  => i >= bestOffset)

Termination == <>(pc = "Done")

StateConstraint == TypeInvariant

\* The .cfg file replaces the standard Naturals Nat with a finite cast that
\* keeps the ordering.
====