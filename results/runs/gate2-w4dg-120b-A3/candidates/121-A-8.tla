---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* Input is a zero-indexed sequence over CharacterSet; the algorithm builds a
\* KMP-style failure function to locate the lexicographically-least rotation
\* of the circular string.
VARIABLES Input, Length, Failure, MatchIdx, LoopPos, BestShift, PC

Vars == <<Input, Length, Failure, MatchIdx, LoopPos, BestShift, PC>>

Sentinel == 9
MaxLen == 2

TypeInvariant ==
    /\ Input \in { s \in Seq(CharacterSet) : Len(s) <= MaxLen }
    /\ Length = Len(Input)
    /\ Failure \in [0..(2 * Length)] -> 0..9
    /\ MatchIdx \in 0..9
    /\ LoopPos \in 0..MaxLen
    /\ BestShift \in (IF Length = 0 THEN {0} ELSE 0..(Length - 1))
    /\ PC \in {"outerCheck", "lookup", "innerLoop", "update",
               "followChain", "postCompare", "increment", "done"}

Init ==
    /\ Input \in { s \in Seq(CharacterSet) : Len(s) <= MaxLen }
    /\ Length = Len(Input)
    /\ Failure = [i \in 0..(2 * Length) |-> Sentinel]
    /\ MatchIdx = Sentinel
    /\ LoopPos = 1
    /\ BestShift = 0
    /\ PC = "outerCheck"

OuterCheck ==
    /\ PC = "outerCheck"
    /\ PC' = IF LoopPos < (2 * Length) THEN "lookup" ELSE "done"
    /\ UNCHANGED <<Input, Length, Failure, MatchIdx, LoopPos, BestShift>>

Lookup ==
    /\ PC = "lookup"
    /\ PC' = "innerLoop"
    /\ MatchIdx' = Failure[(LoopPos + BestShift) % Length]
    /\ UNCHANGED <<Input, Length, Failure, LoopPos, BestShift>>

\* Inner loop: compare the character at the current position against the
\* candidate in the best rotation; the failure function is consulted when
\* they differ while a match is still in progress.
InnerLoop ==
    /\ PC = "innerLoop"
    /\ \/ PC' = "update"
       \/ PC' = "followChain"
    /\ UNCHANGED <<Input, Length, Failure, MatchIdx, LoopPos, BestShift>>

Update ==
    /\ PC = "update"
    /\ MatchIdx # Sentinel
    /\ Input[(LoopPos + BestShift) % Length] # Input[LoopPos % Length]
    /\ Input[LoopPos % Length] < Input[(LoopPos + BestShift) % Length]
    /\ BestShift' = LoopPos % Length
    /\ PC' = "followChain"
    /\ UNCHANGED <<Input, Length, Failure, MatchIdx, LoopPos>>

FollowChain ==
    /\ PC = "followChain"
    /\ PC' = "postCompare"
    /\ MatchIdx' = Failure[MatchIdx]
    /\ UNCHANGED <<Input, Length, Failure, LoopPos, BestShift>>

PostCompare ==
    /\ PC = "postCompare"
    /\ \/ PC' = "increment"
       \/ PC' = "done"
    /\ IF MatchIdx = Sentinel /\ Input[(LoopPos + BestShift) % Length] #
                         Input[LoopPos % Length]
          THEN /\ Input[LoopPos % Length] < Input[(LoopPos + BestShift) % Length]
               /\ BestShift' = LoopPos % Length
          ELSE BestShift' = BestShift
    /\ Failure' = [Failure EXCEPT ![LoopPos] = IF MatchIdx = Sentinel
                                            THEN Sentinel
                                            ELSE MatchIdx + 1]
    /\ UNCHANGED <<Input, Length, MatchIdx, LoopPos>>

Increment ==
    /\ PC = "increment"
    /\ LoopPos' = LoopPos + 1
    /\ PC' = "outerCheck"
    /\ UNCHANGED <<Input, Length, Failure, MatchIdx, BestShift>>

Done ==
    /\ PC = "done"
    /\ PC' = "done"
    /\ UNCHANGED Vars

Stall ==
    /\ PC = "done"
    /\ UNCHANGED Vars

Next ==
    \/ OuterCheck \/ Lookup \/ InnerLoop \/ Update \/ FollowChain
    \/ PostCompare \/ Increment \/ Done \/ Stall

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Lookup) /\ WF_Vars(OuterCheck)

\* Correctness: the identified rotation is lexicographically minimal.
Correctness ==
    /\ PC = "done"
    /\ \A i \in 0..(Length - 1):
         LET rot(k) == << Input[(k + j) % Length] : j \in 0..(Length - 1) >> IN
         rot(BestShift) <= rot(i)

Termination == <>(PC = "done")

\* The .cfg replaces Naturals' Nat with a finite version built from this
\* character set; the extension keeps the definition of Nat available.
[ZSequences]CharacterSet

====