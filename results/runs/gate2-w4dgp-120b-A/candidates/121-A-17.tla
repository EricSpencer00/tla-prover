---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences, FiniteSets

(* Circular strings and zero-indexed sequences are defined in this module   *)
(* rather than imported, because the reference .cfg replaces the Nat       *)
(* operator from Naturals with a finite version tied to the runtime        *)
(* character-set and length bounds.  The algorithm implements Booth's      *)
(* least circular substring routine, which builds a KMP-style failure      *)
(* function as it scans the doubled (wrapped) string.                      *)

CONSTANTS CharacterSet

VARIABLES inputString, length, failure, pattern, loop, bestOffset, pc
vars == <<inputString, length, failure, pattern, loop, bestOffset, pc>>

Sentinel == -1
MinimumChars == 1
MaximumChars == 2

INIT ==
  /\ Cardinality(CharacterSet) >= MinimumChars
  /\ \E s \in [0..(MaximumChars - 1) -> CharacterSet] :
       inputString = s
  /\ length = Len(inputString)
  /\ length >= MinimumChars
  /\ failure = [i \in 0..(2 * length - 1) |-> Sentinel]
  /\ pattern = Sentinel
  /\ loop = 1
  /\ bestOffset = 0
  /\ pc = "outer"

OuterLoop ==
  /\ pc = "outer"
  /\ IF loop < (2 * length)
       THEN /\ pc' = "lookup"
            /\ UNCHANGED <<inputString, length, failure, pattern, loop, bestOffset>>
       ELSE /\ pc' = "terminated"
            /\ UNCHANGED <<inputString, length, failure, pattern, loop, bestOffset>>

LookupFailure ==
  /\ pc = "lookup"
  /\ pattern' = failure[loop - bestOffset]
  /\ pc' = "inner"
  /\ UNCHANGED <<inputString, length, failure, loop, bestOffset>>

\* The inner loop compares the current character against the candidate at
\* the best offset, modulo the length (the wrap round).  It follows the
\* failure chain while the characters differ and a chain remains.
InnerLoop ==
  /\ pc = "inner"
  /\ LET curChar == inputString[loop % length]
         candChar == inputString[(loop - pattern) % length] IN
    /\ IF curChar # candChar /\ pattern # Sentinel
         THEN /\ pc' = "inner"
              /\ UNCHANGED <<inputString, length, failure, pattern, loop, bestOffset>>
         ELSE /\ pc' = "post"
              /\ UNCHANGED <<inputString, length, loop, bestOffset>>
              /\ pattern' = pattern
              /\ curChar' = curChar
              /\ candChar' = candChar
  /\ UNCHANGED <<failure, pattern, loop, bestOffset, pc>>

UpdateOnLess ==
  /\ pc = "inner"
  /\ LET curChar == inputString[loop % length]
         candChar == inputString[(loop - pattern) % length] IN
    /\ curChar < candChar
    /\ bestOffset' = loop
    /\ UNCHANGED <<inputString, length, failure, pattern, loop, pc>>

FollowFailure ==
  /\ pc = "inner"
  /\ pattern # Sentinel
  /\ pattern' = failure[pattern]
  /\ UNCHANGED <<inputString, length, failure, loop, bestOffset, pc>>

\* The post-comparison step applies when the inner loop has exhausted
\* the failure chain without finding a match, or the characters are
\* already equal.  It records a fresh failure link (one past the
\* pattern index, or a sentinel reset) and may update the best offset.
PostComparison ==
  /\ pc = "post"
  /\ LET curChar == inputString[loop % length]
         candChar == inputString[(loop - pattern) % length] IN
    /\ IF curChar # candChar /\ pattern = Sentinel
         THEN IF curChar < candChar
                THEN bestOffset' = loop
                ELSE bestOffset' = bestOffset
              /\ failure' = [failure EXCEPT ![loop] =
                               IF pattern = Sentinel THEN Sentinel ELSE pattern + 1]
         ELSE /\ bestOffset' = bestOffset
              /\ failure' = failure
    /\ pc' = "next"
    /\ UNCHANGED <<inputString, length, pattern, loop>>

\* Advance to the next outer-loop position.
NextStep ==
  /\ pc = "next"
  /\ loop' = loop + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<inputString, length, failure, pattern, bestOffset>>

Stall ==
  /\ pc = "terminated"
  /\ UNCHANGED vars

NEXT ==
  \/ OuterLoop
  \/ LookupFailure
  \/ InnerLoop
  \/ UpdateOnLess
  \/ FollowFailure
  \/ PostComparison
  \/ NextStep
  \/ Stall

Spec == INIT /\ [][NEXT]_vars

TypeInvariant ==
  /\ inputString \in [0..(MaximumChars - 1) -> CharacterSet]
  /\ length = Len(inputString)
  /\ failure \in [0..(2 * length - 1) -> (Sentinel .. length)]
  /\ pattern \in (Sentinel .. length)
  /\ loop \in (Sentinel .. (2 * length))
  /\ bestOffset \in (Sentinel .. (length - 1))
  /\ pc \in {"outer", "lookup", "inner", "post", "next", "terminated"}

\* Correctness: on termination the best offset marks the lexicographically
\* smallest rotation of the input, and it is the smallest such offset.
Correctness ==
  /\ pc = "terminated"
  /\ \A i \in 0..(length - 1) :
       LET candidate(k) == inputString[(bestOffset + k) % length]
           other(k) == inputString[(i + k) % length] IN
         \A k \in 0..(length - 1) : candidate(k) <= other(k)
         /\ (candidate(0) = other(0) => bestOffset <= i)

Termination ==
  \A p \in [pc : {"terminated"}] : <>(p.pc)

====