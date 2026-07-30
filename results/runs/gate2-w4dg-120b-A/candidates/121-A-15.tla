---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet, Nat

RECURSIVE Rotations(_)
Rotations(s) ==
  IF Len(s) = 0 THEN {}
  ELSE
    LET r == s \o s IN
    { SubSeq(r, k, k + Len(s) - 1) : k \in 1 .. Len(s) }

Sentinel == 0 - 1
MaxLen == 2

VARIABLES input, length, failure, pattern, loop, best, pc

vars == <<input, length, failure, pattern, loop, best, pc>>

TypeInvariant ==
  /\ input \in { s \in Seq(CharacterSet) : Len(s) <= MaxLen }
  /\ length = Len(input)
  /\ failure \in [0 .. (2 * MaxLen - 1) -> {Sentinel} \cup (0 .. MaxLen - 1)]
  /\ pattern \in {Sentinel} \cup (0 .. MaxLen - 1)
  /\ loop \in 1 .. (2 * MaxLen)
  /\ best \in 0 .. (MaxLen - 1)
  /\ pc \in {"outer", "lookup", "inner", "updateBestLess", "follow", "postCmp", "increment", "done"}

Init ==
  /\ input \in { s \in Seq(CharacterSet) : Len(s) <= MaxLen }
  /\ length = Len(input)
  /\ failure = [i \in 0 .. (2 * MaxLen - 1) |-> Sentinel]
  /\ pattern = Sentinel
  /\ loop = 1
  /\ best = 0
  /\ pc = "outer"

OuterLoop ==
  /\ pc = "outer"
  /\ IF loop < (2 * MaxLen)
       THEN /\ pc' = "lookup"
            /\ pattern' = Sentinel
       ELSE /\ pc' = "done"
            /\ UNCHANGED <<pattern, loop>>
  /\ UNCHANGED <<input, length, failure, best>>

Lookup ==
  /\ pc = "lookup"
  /\ pattern' = failure[loop]
  /\ pc' = "inner"
  /\ UNCHANGED <<input, length, failure, loop, best>>

CurrentChar == input[((loop - 1) % length) + 1]
CandidateChar == input[((best + loop - 1) % length) + 1]

InnerLoop ==
  /\ pc = "inner"
  /\ IF CurrentChar = CandidateChar
       THEN /\ pc' = "postCmp"
            /\ UNCHANGED pattern
       ELSE IF pattern # Sentinel
            THEN /\ pc' = "inner"
                 /\ pattern' = failure[pattern]
            ELSE /\ pc' = "postCmp"
                 /\ UNCHANGED pattern
  /\ UNCHANGED <<input, length, failure, loop, best>>

UpdateBestLess ==
  /\ pc = "updateBestLess"
  /\ CurrentChar < CandidateChar
  /\ best' = (best + loop) % length
  /\ pc' = "follow"
  /\ UNCHANGED <<input, length, failure, pattern, loop>>

Follow ==
  /\ pc = "follow"
  /\ pattern' = failure[pattern]
  /\ pc' = "postCmp"
  /\ UNCHANGED <<input, length, failure, loop, best>>

PostCmp ==
  /\ pc = "postCmp"
  /\ IF CurrentChar # CandidateChar /\ pattern = Sentinel
       THEN IF CurrentChar < CandidateChar
              THEN best' = (best + loop) % length
              ELSE best' = best
       ELSE best' = best
  /\ failure' = [failure EXCEPT ![loop] = IF pattern = Sentinel THEN Sentinel ELSE pattern + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<input, length, pattern, loop>>

Increment ==
  /\ pc = "increment"
  /\ loop' = loop + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<input, length, failure, pattern, best>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop
  \/ Lookup
  \/ InnerLoop
  \/ UpdateBestLess
  \/ Follow
  \/ PostCmp
  \/ Increment
  \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(Lookup) /\ WF_vars(Increment)

RotationAt(k) == SubSeq(input \o input, k + 1, k + length)

Correctness ==
  /\ \A k \in 0 .. (length - 1) : RotationAt(best) <= RotationAt(k)
  /\ \A k \in 0 .. (length - 1) : RotationAt(best) = RotationAt(k) => best <= k

Termination == <>(pc = "done")

====