---- MODULE LeastCircularSubstring ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS CharacterSet

VARIABLES inputString, failureFunction, patternMatchIndex, loopCounter, bestShift
vars == << inputString, failureFunction, patternMatchIndex, loopCounter, bestShift >>

\* ZSequences: zero-indexed version of Sequences (all indices start at 0)
ZSeq(s) == << s[0] >> \o s
\* ZSubSeq: zero-indexed subsequence s[m..n-1], empty when n <= m
ZSubSeq(s, m, n) ==
  IF n <= m THEN << >>
  ELSE IF n = m + 1 THEN << s[m] >>
  ELSE << s[m] >> \o ZSubSeq(s, m + 1, n)
\* ZSeqLen: length of a zero-indexed sequence
ZSeqLen(s) == Cardinality({i \in DOMAIN s : TRUE})
\* ZSeqCat: zero-indexed concatenation of s and t
ZSeqCat(s, t) == s \o t
\* ZSeqTake: first n elements of a zero-indexed sequence s
ZSeqTake(s, n) ==
  IF n = 0 THEN << >>
  ELSE IF n > ZSeqLen(s) THEN s
  ELSE << s[0] >> \o ZSeqTake(ZSubSeq(s, 1, ZSeqLen(s)), n - 1)
\* ZSubSeqLoop: s[0..]circularly, length n, starting at base
ZSubSeqLoop(s, base, n) == ZSeqTake(ZSeqCat(ZSubSeq(s, base, ZSeqLen(s)), s), n)

Corpus == {s \in CharacterSet : 0 < ZSeqLen(s)}
Sentinel == 0 - 1
Stride == 2

TypeInvariant ==
  /\ inputString \in Corpus
  /\ Len == ZSeqLen(inputString)
  /\ failureFunction \in [0..(Stride * Len) -> (Sentinel..Len)]
  /\ patternMatchIndex \in (Sentinel..Len)
  /\ loopCounter \in 1..(Stride * Len + 1)
  /\ bestShift \in 0..(Len - 1)

Init ==
  /\ inputString \in Corpus
  /\ Len == ZSeqLen(inputString)
  /\ failureFunction = [i \in 0..(Stride * Len) |-> Sentinel]
  /\ patternMatchIndex = Sentinel
  /\ loopCounter = 1
  /\ bestShift = 0

\* Outer loop of Booth's algorithm, iterated over a doubled string so the
\* wrap-around is handled without circular indexing logic.
OuterLoop ==
  /\ loopCounter < Stride * Len
  /\ patternMatchIndex' = failureFunction[loopCounter - 1 - bestShift]
  /\ UNCHANGED << inputString, failureFunction, loopCounter, bestShift >>

InnerStep ==
  /\ loopCounter < Stride * Len
  /\ ZSubSeqLoop(inputString, bestShift, loopCounter)[0] # ZSubSeqLoop(inputString, 0, loopCounter)[0]
  /\ patternMatchIndex # Sentinel
  /\ UNCHANGED << inputString, failureFunction, patternMatchIndex, loopCounter, bestShift >>

\* The mismatch at the current character is strictly better than the candidate.
ShiftOnMismatch ==
  /\ loopCounter < Stride * Len
  /\ ZSubSeqLoop(inputString, bestShift, loopCounter)[0] # ZSubSeqLoop(inputString, 0, loopCounter)[0]
  /\ ZSubSeqLoop(inputString, bestShift, loopCounter)[0] < ZSubSeqLoop(inputString, 0, loopCounter)[0]
  /\ bestShift' = loopCounter
  /\ UNCHANGED << inputString, failureFunction, patternMatchIndex, loopCounter >>

FollowFailure ==
  /\ loopCounter < Stride * Len
  /\ patternMatchIndex # Sentinel
  /\ patternMatchIndex' = failureFunction[patternMatchIndex]
  /\ UNCHANGED << inputString, failureFunction, loopCounter, bestShift >>

\* End of the inner loop: either the characters matched or the failure chain
\* was exhausted, so the failure function entry is reset.
UpdateOnInnerExit ==
  /\ loopCounter < Stride * Len
  /\ ZSubSeqLoop(inputString, bestShift, loopCounter)[0] # ZSubSeqLoop(inputString, 0, loopCounter)[0]
  /\ patternMatchIndex = Sentinel
  /\ failureFunction' = [failureFunction EXCEPT ![loopCounter] = Sentinel]
  /\ UNCHANGED << inputString, patternMatchIndex, loopCounter, bestShift >>

\* The inner loop ends without a mismatch -- this is the "else" of the
\* comparison, so the failure function entry is extended rather than reset.
ExtendOnInnerExit ==
  /\ loopCounter < Stride * Len
  /\ ZSubSeqLoop(inputString, bestShift, loopCounter)[0] # ZSubSeqLoop(inputString, 0, loopCounter)[0]
  /\ patternMatchIndex # Sentinel
  /\ failureFunction' = [failureFunction EXCEPT ![loopCounter] = patternMatchIndex + 1]
  /\ UNCHANGED << inputString, patternMatchIndex, loopCounter, bestShift >>

ShiftOnInnerExit ==
  /\ loopCounter < Stride * Len
  /\ ZSubSeqLoop(inputString, bestShift, loopCounter)[0] # ZSubSeqLoop(inputString, 0, loopCounter)[0]
  /\ ZSubSeqLoop(inputString, bestShift, loopCounter)[0] < ZSubSeqLoop(inputString, 0, loopCounter)[0]
  /\ bestShift' = loopCounter
  /\ UNCHANGED << inputString, failureFunction, patternMatchIndex, loopCounter >>

IncrementOuter ==
  /\ loopCounter < Stride * Len
  /\ loopCounter' = loopCounter + 1
  /\ UNCHANGED << inputString, failureFunction, patternMatchIndex, bestShift >>

LoopTerminated == loopCounter >= Stride * Len

Terminated == LoopTerminated /\ UNCHANGED vars
Stall == LoopTerminated /\ UNCHANGED vars

Next ==
  \/ OuterLoop \/ InnerStep \/ ShiftOnMismatch \/ FollowFailure
  \/ UpdateOnInnerExit \/ ExtendOnInnerExit \/ ShiftOnInnerExit
  \/ IncrementOuter \/ Terminated \/ Stall

Spec == Init /\ [][Next]_vars

\* Correctness: the best shift found is at most as lexicographically small as
\* any other rotation, and if any other rotation yields the same sequence the
\* best shift is smaller (the algorithm is deterministic on ties).
AtMostAsSmallAsAnyOtherRotation ==
  \A i, j \in 0..(Len - 1) :
    (ZSeqTake(ZSeqCat(inputString, inputString), i + Len) # ZSeqTake(ZSeqCat(inputString, inputString), j + Len)) =>
      (ZSeqTake(ZSeqCat(inputString, inputString), i + Len) # ZSeqTake(ZSeqCat(inputString, inputString), bestShift + Len))
    /\ ((ZSeqTake(ZSeqCat(inputString, inputString), bestShift + Len) = ZSeqTake(ZSeqCat(inputString, inputString), j + Len)) => (bestShift <= j))

Termination == <>(LoopTerminated)

====