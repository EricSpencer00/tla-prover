---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

ASSUME CharacterSet \subseteq Nat

Sentinel == 0
MaxLen == 2
MaxChar == Max(CharacterSet)

Rotations(str) == { SubSeq(str, i, Len(str)) @@ SubSeq(str, 1, i - 1) : i \in 1 .. Len(str) }

\* The failure function stores indices; "Sentinel" means "undefined".
Indices == 0 .. (2 * MaxLen)
WithSentinel(S) == S \cup {Sentinel}

VARIABLES string, flen, fail, matchIdx, loopIdx, bestOff, pc

vars == <<string, flen, fail, matchIdx, loopIdx, bestOff, pc>>

TypeInvariant ==
  /\ string \in [1 .. MaxLen -> CharacterSet]
  /\ flen = Len(string)
  /\ fail \in [Indices -> WithSentinel(Indices)]
  /\ matchIdx \in WithSentinel(Indices)
  /\ loopIdx \in Indices
  /\ bestOff \in 1 .. MaxLen
  /\ pc \in {"outer", "lookup", "inner", "update", "follow", "post", "terminating"}

Init ==
  /\ \E s \in [1 .. MaxLen -> CharacterSet] : string = s
  /\ flen = Len(string)
  /\ fail = [k \in Indices |-> Sentinel]
  /\ matchIdx = Sentinel
  /\ loopIdx = 1
  /\ bestOff = 1
  /\ pc = "outer"

OuterLoop ==
  /\ pc = "outer"
  /\ loopIdx < 2 * flen
  /\ pc' = "lookup"
  /\ UNCHANGED <<string, flen, fail, matchIdx, loopIdx, bestOff>>

LookupFailure ==
  /\ pc = "lookup"
  /\ matchIdx' = fail[loopIdx - bestOff]
  /\ pc' = "inner"
  /\ UNCHANGED <<string, flen, fail, loopIdx, bestOff>>

\* The pattern-match index is the KMP-like index into the failure function.
InnerCompare ==
  /\ pc = "inner"
  /\ matchIdx # Sentinel
  /\ string[(loopIdx % flen) + 1] # string[((bestOff + matchIdx) % flen) + 1]
  /\ pc' = "inner"
  /\ UNCHANGED <<string, flen, fail, matchIdx, loopIdx, bestOff>>

UpdateBestLess ==
  /\ pc = "inner"
  /\ string[(loopIdx % flen) + 1] < string[((bestOff + matchIdx) % flen) + 1]
  /\ bestOff' = (loopIdx % flen) + 1
  /\ pc' = "follow"
  /\ UNCHANGED <<string, flen, fail, matchIdx, loopIdx>>

FollowChain ==
  /\ pc = "follow"
  /\ matchIdx' = fail[matchIdx]
  /\ pc' = "post"
  /\ UNCHANGED <<string, flen, fail, loopIdx, bestOff>>

PostMismatch ==
  /\ pc = "post"
  /\ matchIdx # Sentinel
  /\ string[(loopIdx % flen) + 1] # string[((bestOff + matchIdx) % flen) + 1]
  /\ matchIdx = Sentinel
  /\ string[(loopIdx % flen) + 1] < string[((bestOff + matchIdx) % flen) + 1]
  /\ bestOff' = (loopIdx % flen) + 1
  /\ fail' = [fail EXCEPT ![loopIdx - bestOff] = Sentinel]
  /\ pc' = "advance"
  /\ UNCHANGED <<string, flen, matchIdx, loopIdx>>

\* Extend the matched prefix by one (the KMP extension step).
PostExtend ==
  /\ pc = "post"
  /\ matchIdx # Sentinel
  /\ fail' = [fail EXCEPT ![loopIdx - bestOff] = matchIdx + 1]
  /\ pc' = "advance"
  /\ UNCHANGED <<string, flen, matchIdx, loopIdx, bestOff>>

AdvanceLoop ==
  /\ pc = "advance"
  /\ loopIdx' = loopIdx + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<string, flen, fail, matchIdx, bestOff>>

\* The outer loop runs past the string length, but its index still fits.
AdvanceLoop2 ==
  /\ pc = "post"
  /\ pc' = "advance"
  /\ UNCHANGED <<string, flen, fail, matchIdx, loopIdx, bestOff>>

Terminate ==
  /\ pc = "outer"
  /\ loopIdx >= 2 * flen
  /\ pc' = "terminating"
  /\ UNCHANGED <<string, flen, fail, matchIdx, loopIdx, bestOff>>

Stall ==
  /\ pc = "terminating"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop \/ LookupFailure \/ InnerCompare \/ UpdateBestLess
  \/ FollowChain \/ PostMismatch \/ PostExtend \/ AdvanceLoop
  \/ AdvanceLoop2 \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(AdvanceLoop)

Correctness ==
  /\ (bestOff - 1) % flen + 1 \in { i \in 1 .. flen : Rotations(string) = {Rotations(string)[i]} }
  /\ \A i \in 1 .. flen : Rotations(string)[(bestOff - 1) % flen + 1] <= Rotations(string)[i]

Termination == <>(pc = "terminating")

====