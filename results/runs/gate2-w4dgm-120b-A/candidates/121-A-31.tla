---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences, ZSequences

CONSTANTS CharacterSet

\* The lexicographically-least circular substring algorithm processes a
\* zero-indexed string whose characters are drawn from CharacterSet,
\* building a failure function like KMP's to run in linear time.
\* No actor: a single sequential loop tree drives the whole algorithm.

\* Types/shape: string is a zero-indexed sequence; FailureFn is indexed
\* from 0 up to twice the string length (the "doubled" scan that handles
\* wrap-around); Sentinel marks an undefined failure entry; PC is the
\* labeled-step program counter.
\* The invariant checks every shape claim; the correctness property
\* checks that the winning rotation is truly the lexical minimum.
\* StringChoice makes the input nondeterministic over the whole corpus.

Sentinel == 0
MaxLen == 2

VARIABLES string, length, failureFn, matchIdx, loopCounter, bestOffset, pc

vars == <<string, length, failureFn, matchIdx, loopCounter, bestOffset, pc>>

TypeInvariant ==
  /\ string \in Seq(CharacterSet)
  /\ length = Len(string)
  /\ failureFn \in [0..(MaxLen * MaxLen) -> 0..MaxLen]
  /\ matchIdx \in 0..MaxLen
  /\ loopCounter \in 0..MaxLen
  /\ bestOffset \in 0..(IF length = 0 THEN 1 ELSE length - 1)
  /\ pc \in {"OuterLoop", "Lookup", "InnerLoop", "UpdateBest", "FollowLink", "PostLoop", "Done"}

StringChoice ==
  /\ \E s \in Seq(CharacterSet) : string' = s
  /\ length' = Len(string)
  /\ UNCHANGED <<failureFn, matchIdx, loopCounter, bestOffset, pc>>

Init ==
  /\ stringChoice
  /\ failureFn = [i \in 0..(MaxLen * MaxLen) |-> Sentinel]
  /\ matchIdx = Sentinel
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "OuterLoop"

OuterLoop ==
  /\ pc = "OuterLoop"
  /\ pc' = "Lookup"
  /\ UNCHANGED <<string, length, failureFn, matchIdx, loopCounter, bestOffset>>

Lookup ==
  /\ pc = "Lookup"
  /\ matchIdx' = failureFn[loopCounter - 1]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<string, length, failureFn, loopCounter, bestOffset>>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ (string[(loopCounter - 1) % length] # string[(bestOffset + loopCounter - 1) % length] /\ matchIdx # Sentinel)
  /\ pc' = "UpdateBest"
  /\ UNCHANGED <<string, length, failureFn, matchIdx, loopCounter, bestOffset>>

UpdateBest ==
  /\ pc = "UpdateBest"
  /\ IF string[(loopCounter - 1) % length] < string[(bestOffset + loopCounter - 1) % length]
     THEN bestOffset' = (loopCounter + bestOffset) % length
     ELSE bestOffset' = bestOffset
  /\ pc' = "FollowLink"
  /\ UNCHANGED <<string, length, failureFn, matchIdx, loopCounter>>

FollowLink ==
  /\ pc = "FollowLink"
  /\ matchIdx' = failureFn[matchIdx]
  /\ pc' = "PostLoop"
  /\ UNCHANGED <<string, length, failureFn, loopCounter, bestOffset>>

PostLoop ==
  /\ pc = "PostLoop"
  /\ IF /\ string[(loopCounter - 1) % length] # string[(bestOffset + loopCounter - 1) % length]
        /\ matchIdx = Sentinel
       THEN IF string[(loopCounter - 1) % length] < string[(bestOffset + loopCounter - 1) % length]
            THEN bestOffset' = (loopCounter + bestOffset) % length
            ELSE bestOffset' = bestOffset
       ELSE bestOffset' = bestOffset
  /\ failureFn' = [failureFn EXCEPT ![loopCounter - 1] =
                     IF string[(loopCounter - 1) % length] = string[(bestOffset + loopCounter - 1) % length]
                     THEN matchIdx + 1
                     ELSE Sentinel]
  /\ loopCounter' = (loopCounter + 1) % (MaxLen + 1)
  /\ pc' = IF loopCounter + 1 <= MaxLen THEN "OuterLoop" ELSE "Done"
  /\ UNCHANGED <<string, length, matchIdx>>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop \/ Lookup \/ InnerLoop \/ UpdateBest \/ FollowLink \/ PostLoop \/ Done
  \/ stringChoice

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(Lookup) /\ WF_vars(InnerLoop)
        /\ WF_vars(UpdateBest) /\ WF_vars(FollowLink) /\ WF_vars(PostLoop)

Termination == pc = "Done"

Correctness ==
  /\ (pc = "Done" => \A i \in 0..(length - 1) :
        \/ (string[(bestOffset + i) % length] \in CharacterSet /\ bestOffset + i \in 0..(2 * MaxLen))
        \/ (string[(bestOffset + i) % length] > string[(bestOffset) % length]
            \/ (string[(bestOffset + i) % length] = string[(bestOffset) % length] /\ i >= bestOffset))
      )
  /\ ((pc = "Done") => Cardinality(CharacterSet) < 2 => bestOffset = 0)
  /\ (pc = "Done" => (\A x, y \in 0..(length - 1) :
        (string[(bestOffset + x) % length] = string[(bestOffset + y) % length]) => x <= y))
  /\ (pc = "Done" => (\A a, b \in 0..(length - 1) :
        ((string[(bestOffset + a) % length] = string[(bestOffset) % length] /\ string[(bestOffset + b) % length] = string[(bestOffset) % length])
          => a <= b)))

====