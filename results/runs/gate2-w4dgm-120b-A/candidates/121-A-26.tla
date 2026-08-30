---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

(* ===================================================================== *)
(*  Types and utility definitions (zero-indexed sequences, replacement for *)
(*  a full ZSequences module, bound by a configurable CharacterSet.)       *)
(* ===================================================================== *)

\* Zero-indexed sequence: the head is at index 0, not 1.
SeqOf(elems) == [i \in 0 .. Len(elems) - 1 |-> elems[i + 1]]

\* Characters are drawn from a finite set of natural numbers, bound by
\* CharacterSet (overridden in the .cfg to be a finite subset of Nat).
CHAR == 0 .. CharacterSet - 1

\* Sentinel value meaning "no failure link (yet) computed."
Sentinel == CharacterSet

\* Index in the failure-function chain, or Sentinel at the chain start.
Link == 0 .. 2 * CharacterSet - 1 \cup {Sentinel}

\* The lexicographic relation on fixed-length strings.
LexLeq(s, t) ==
  \/ (s = t)
  \/ \E i \in 1 .. Len(s) :
       /\ \A j \in 1 .. i - 1 : s[j] = t[j]
       /\ s[i] < t[i]

(* ===================================================================== *)
(*  System state.                                                       *)
(* ===================================================================== *)
VARIABLES string, strLen, failure, matchAt, loopIdx, bestOff, pc

vars == <<string, strLen, failure, matchAt, loopIdx, bestOff, pc>>

(* The corpus: every finite zero-indexed sequence over the character set. *)
Corpus == UNION { [i \in 0 .. n - 1 |-> f[i + 1]] : n \in 0 .. CharacterSet, f \in [1 .. n -> CHAR] }

TypeOK ==
  /\ string \in Corpus
  /\ strLen = Len(string)
  /\ failure \in [0 .. 2 * CharacterSet - 1 -> Link]
  /\ matchAt \in Link
  /\ loopIdx \in 1 .. 2 * CharacterSet
  /\ bestOff \in 0 .. CharacterSet - 1
  /\ pc \in {"outerCheck", "lookup", "innerLoop", "candidateBetter",
             "followChain", "postCompare", "terminate"}

Init ==
  /\ \E s \in Corpus :
       /\ string = s
       /\ strLen = Len(s)
  /\ failure = [i \in 0 .. 2 * CharacterSet - 1 |-> Sentinel]
  /\ matchAt = Sentinel
  /\ loopIdx = 1
  /\ bestOff = 0
  /\ pc = "outerCheck"

OuterLoop ==
  /\ loopIdx < 2 * strLen
  /\ pc' = "lookup"
  /\ UNCHANGED <<string, strLen, failure, matchAt, loopIdx, bestOff>>

LookupFailure ==
  /\ pc = "lookup"
  /\ matchAt' = failure[loopIdx - bestOff]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<string, strLen, failure, loopIdx, bestOff>>

\* The inner loop walks the failure chain, comparing character at the
\* current candidate offset against the character at the best offset so far.
InnerLoop ==
  /\ pc = "innerLoop"
  /\ /\ string[(loopIdx) % strLen] # string[(bestOff) % strLen]
     /\ matchAt # Sentinel
  /\ pc' = "candidateBetter"
  /\ UNCHANGED <<string, strLen, failure, matchAt, loopIdx, bestOff>>

CandidateBetter ==
  /\ pc = "candidateBetter"
  /\ /\ string[(loopIdx) % strLen] < string[(bestOff) % strLen]
     /\ bestOff' = loopIdx % strLen
  /\ pc' = "followChain"
  /\ UNCHANGED <<string, strLen, failure, matchAt, loopIdx>>

FollowChain ==
  /\ pc = "followChain"
  /\ matchAt' = failure[matchAt]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<string, strLen, failure, loopIdx, bestOff>>

PostCompare ==
  /\ pc = "innerLoop"
  /\ \/ string[(loopIdx) % strLen] # string[(bestOff) % strLen]
        /\ matchAt = Sentinel
     \/ pc = "postCompare"
  /\ \/ /\ string[(loopIdx) % strLen] < string[(bestOff) % strLen]
         /\ bestOff' = loopIdx % strLen
        /\ failure' = [failure EXCEPT ![loopIdx - bestOff] = Sentinel]
     \/ /\ failure' = [failure EXCEPT ![loopIdx - bestOff] = matchAt + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<string, strLen, matchAt, loopIdx>>

Increment ==
  /\ pc = "postCompare"
  /\ loopIdx' = loopIdx + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<string, strLen, failure, matchAt, bestOff>>

Terminate ==
  /\ pc = "outerCheck"
  /\ loopIdx >= 2 * strLen
  /\ pc' = "terminate"
  /\ UNCHANGED <<string, strLen, failure, matchAt, loopIdx, bestOff>>

\* Stuttering in the final, terminated state.
Stall ==
  /\ pc = "terminate"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop \/ LookupFailure \/ InnerLoop \/ CandidateBetter
  \/ FollowChain \/ PostCompare \/ Increment \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(LookupFailure)
        /\ WF_vars(InnerLoop) /\ WF_vars(CandidateBetter) /\ WF_vars(FollowChain)
        /\ WF_vars(PostCompare) /\ WF_vars(Increment) /\ WF_vars(Terminate)

TypeInvariant ==
  /\ string \in Corpus
  /\ strLen = Len(string)
  /\ failure \in [0 .. 2 * CharacterSet - 1 -> Link]
  /\ matchAt \in Link
  /\ loopIdx \in 1 .. 2 * CharacterSet
  /\ bestOff \in 0 .. CharacterSet - 1
  /\ pc \in {"outerCheck", "lookup", "innerLoop", "candidateBetter",
             "followChain", "postCompare", "terminate"}

(* The lexicographically minimal rotation of the input string, at offset   *)
(* bestOff, is no greater than any other rotation and, if equal, has the   *)
(* smallest shift value.                                                   *)
Correctness ==
  /\ \A i \in 1 .. strLen : SeqOf(string)[bestOff .. bestOff + strLen - 1]
                             <= SeqOf(string)[i .. i + strLen - 1]
  /\ \A i \in 1 .. strLen :
       (SeqOf(string)[bestOff .. bestOff + strLen - 1]
          = SeqOf(string)[i .. i + strLen - 1]) => bestOff <= i

Termination == <>(pc = "terminate")

====