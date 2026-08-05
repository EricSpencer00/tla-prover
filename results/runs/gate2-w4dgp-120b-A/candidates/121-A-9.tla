---- MODULE LeastCircularSubstring ----
EXTENDS Integers, FiniteSets, Sequences, ZSequences

CONSTANTS CharacterSet

\* The failure function array tracks a KMP-like chain; the sentinel value marks an
\* undefined entry. Strings are zero-indexed (the ZSequences version) and the
\* algorithm iterates up to twice the length to cover the doubled (circular) view.
Sentinel == -1

VARIABLES inputString, strLength, failFunc, patIdx, loopCtr, bestShift, pc

vars == <<inputString, strLength, failFunc, patIdx, loopCtr, bestShift, pc>>

\* The corpus is the sequence of every string over the character set up to the
\* configured maximum length (LengthBound, set in the .cfg with a real number).
Corpus == Union({[1..n -> CharacterSet] : n \in 1..LengthBound})

Init ==
  /\ inputString \in Corpus
  /\ strLength = Len(inputString)
  /\ failFunc \in [0..2*strLength -> {Sentinel} \cup (0..2*strLength)]
  /\ patIdx = Sentinel
  /\ loopCtr = 1
  /\ bestShift = 0
  /\ pc = "outer_check"

OuterCheck ==
  /\ pc = "outer_check"
  /\ IF loopCtr < 2*strLength
       THEN /\ pc' = "lookup_fail"
            /\ UNCHANGED <<inputString, strLength, failFunc, patIdx, loopCtr, bestShift>>
       ELSE /\ pc' = "terminated"
            /\ UNCHANGED vars

LookupFail ==
  /\ pc = "lookup_fail"
  /\ patIdx' = failFunc[loopCtr - bestShift]
  /\ pc' = "compare_loop"
  /\ UNCHANGED <<inputString, strLength, failFunc, loopCtr, bestShift>>

\* Comparing the doubled string at position loopCtr (modulo length) against the
\* candidate rotation at position patIdx (modulo length).
CompareLoop ==
  /\ pc = "compare_loop"
  /\ inputString[(loopCtr % strLength) + 1] # inputString[(patIdx % strLength) + 1]
  /\ patIdx # Sentinel
  /\ pc' = "compare_loop"
  /\ UNCHANGED <<inputString, strLength, failFunc, patIdx, loopCtr, bestShift>>

UpdateBestLess ==
  /\ pc = "compare_loop"
  /\ inputString[(loopCtr % strLength) + 1] < inputString[(patIdx % strLength) + 1]
  /\ bestShift' = loopCtr
  /\ pc' = "follow_chain"
  /\ UNCHANGED <<inputString, strLength, failFunc, patIdx, loopCtr>>

FollowChain ==
  /\ pc = "compare_loop"
  /\ inputString[(loopCtr % strLength) + 1] # inputString[(patIdx % strLength) + 1]
  /\ patIdx = Sentinel
  /\ pc' = "post_compare"
  /\ UNCHANGED <<inputString, strLength, failFunc, patIdx, loopCtr, bestShift>>

PostCompare ==
  /\ pc = "post_compare"
  /\ LET cand == inputString[(patIdx % strLength) + 1] IN
       LET cur == inputString[(loopCtr % strLength) + 1] IN
         /\ (cur # cand /\ cand # Sentinel) => (cur < cand => bestShift' = loopCtr)
         /\ failFunc' = [failFunc EXCEPT ![loopCtr - bestShift] =
                            IF patIdx = Sentinel THEN Sentinel ELSE patIdx + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, strLength, patIdx, loopCtr>>

Increment ==
  /\ pc = "increment"
  /\ loopCtr' = loopCtr + 1
  /\ pc' = "outer_check"
  /\ UNCHANGED <<inputString, strLength, failFunc, patIdx, bestShift>>

Stall ==
  /\ pc = "terminated"
  /\ UNCHANGED vars

Next == OuterCheck \/ LookupFail \/ CompareLoop \/ UpdateBestLess \/ FollowChain
        \/ PostCompare \/ Increment \/ Stall

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E _ : OuterCheck \/ LookupFail \/ Increment)
        /\ WF_vars(\E _ : CompareLoop \/ UpdateBestLess \/ FollowChain \/ PostCompare)

TypeInvariant ==
  /\ inputString \in Corpus
  /\ strLength = Len(inputString)
  /\ failFunc \in [0..2*strLength -> {Sentinel} \cup (0..2*strLength)]
  /\ patIdx \in {Sentinel} \cup (0..2*strLength)
  /\ loopCtr \in 1..2*strLength
  /\ bestShift \in 0..(strLength - 1)
  /\ pc \in {"outer_check", "lookup_fail", "compare_loop", "post_compare",
             "increment", "terminated"}

\* Lexicographic minimality: the rotation at bestShift is at most every other
\* rotation, and equal rotations are broken by preferring the smaller shift.
Correctness ==
  /\ \A shift \in 0..(strLength - 1) :
       (inputString[(bestShift % strLength) + 1] = inputString[(shift % strLength) + 1])
         => bestShift <= shift
  /\ \A shift \in 0..(strLength - 1) :
       (inputString[(bestShift % strLength) + 1] < inputString[(shift % strLength) + 1])

Termination ==
  \A shift \in 0..(strLength - 1) :
    (\A j \in 0..(strLength - 1) :
       inputString[(shift % strLength) + 1] = inputString[(j % strLength) + 1])
      ~> (\A j \in 0..(strLength - 1) :
            inputString[(bestShift % strLength) + 1] = inputString[(j % strLength) + 1])

====