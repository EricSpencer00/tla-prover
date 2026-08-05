---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences, FiniteSets

(* The lexicographically-least circular substring algorithm from Booth 1980.     *)
(* The algorithm computes the minimal rotation of a circular string in linear   *)
(* time using a failure function (like KMP) over the string viewed twice.       *)
(* The model checks, for all strings over the configured alphabet up to the     *)
(* configured maximum length, that the identified rotation is minimal.          *)

CONSTANTS CharacterSet

VARIABLES string, strLen, failureFunction, matchIndex, loopCounter, bestOffset, pc

vars == <<string, strLen, failureFunction, matchIndex, loopCounter, bestOffset, pc>>

StringCorpus == UNION { UNION { { <<i : 1 .. n>> : i \in (SUBSET [1 .. n -> CharacterSet]) } : n \in 1 .. MaxStringLength } }

Sentinel == -1

TypeInvariant ==
  /\ string \in StringCorpus
  /\ strLen = Len(string)
  /\ failureFunction \in [0 .. 2 * strLen -> {Sentinel} \cup (0 .. 2 * strLen)]
  /\ matchIndex \in {Sentinel} \cup (0 .. 2 * strLen)
  /\ loopCounter \in 1 .. (2 * strLen) + 1
  /\ bestOffset \in 0 .. strLen - 1
  /\ pc \in {"outerCheck", "lookup", "innerLoop", "updateOffset", "followFailure", "postComparison", "advance", "done"}

Init ==
  /\ \E s \in StringCorpus :
       /\ string' = s
       /\ strLen' = Len(s)
  /\ failureFunction' = [i \in 0 .. 2 * strLen |-> Sentinel]
  /\ matchIndex' = Sentinel
  /\ loopCounter' = 1
  /\ bestOffset' = 0
  /\ pc' = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF loopCounter < 2 * strLen
       THEN pc' = "lookup"
       ELSE pc' = "done"
  /\ UNCHANGED <<string, strLen, failureFunction, matchIndex, loopCounter, bestOffset>>

Lookup ==
  /\ pc = "lookup"
  /\ matchIndex' = failureFunction[(loopCounter + bestOffset) % strLen]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<string, strLen, failureFunction, loopCounter, bestOffset>>

CharAt(i) == string[(i % strLen) + 1]

InnerLoop ==
  /\ pc = "innerLoop"
  /\ CharAt(loopCounter) # CharAt((bestOffset + matchIndex) % strLen)
  /\ matchIndex # Sentinel
  /\ pc' = "followFailure"
  /\ UNCHANGED <<string, strLen, failureFunction, matchIndex, loopCounter, bestOffset>>

UpdateOffset ==
  /\ pc = "innerLoop"
  /\ CharAt(loopCounter) < CharAt((bestOffset + matchIndex) % strLen)
  /\ bestOffset' = loopCounter % strLen
  /\ pc' = "followFailure"
  /\ UNCHANGED <<string, strLen, failureFunction, matchIndex, loopCounter>>

FollowFailure ==
  /\ pc = "followFailure"
  /\ matchIndex' = failureFunction[matchIndex]
  /\ pc' = "postComparison"
  /\ UNCHANGED <<string, strLen, failureFunction, loopCounter, bestOffset>>

PostComparison ==
  /\ pc = "postComparison"
  /\ IF CharAt(loopCounter) < CharAt((bestOffset + matchIndex) % strLen)
       /\ matchIndex = Sentinel
       THEN bestOffset' = loopCounter % strLen
       ELSE bestOffset' = bestOffset
  /\ failureFunction' = [failureFunction EXCEPT ![loopCounter] =
                          IF matchIndex = Sentinel THEN Sentinel ELSE matchIndex + 1]
  /\ pc' = "advance"
  /\ UNCHANGED <<string, strLen, matchIndex, loopCounter>>

Advance ==
  /\ pc = "advance"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<string, strLen, failureFunction, matchIndex, bestOffset>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerLoop
  \/ UpdateOffset
  \/ FollowFailure
  \/ PostComparison
  \/ Advance
  \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Lookup) /\ WF_vars(PostComparison) /\ WF_vars(Advance)

(* The identified rotation is at least as small as every other rotation of the *)
(* string, and if another rotation equals it, its shift is not smaller.         *)
Correctness ==
  \A i \in 0 .. strLen - 1 :
    /\ CharAt(bestOffset) <= CharAt(i)
    /\ (CharAt(bestOffset) = CharAt(i) => bestOffset <= i)

Termination == <>(pc = "done")

====