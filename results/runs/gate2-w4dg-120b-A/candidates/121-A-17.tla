---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

(* The lexicographically-least circular substring algorithm from Booth (1980).  *)
(* The input string is chosen nondeterministically from all sequences over the    *)
(* character set, so the model must verify correctness for the entire corpus.     *)

CONSTANTS CharacterSet, Nat
Sentinel == 9

VARIABLES
  string,               \* the input, a zero-indexed sequence of characters from CharacterSet
  length,               \* length of the input string
  failure,              \* failure function array (indexed to twice the string length)
  pattern,              \* current failure function lookup value
  outer,                \* outer loop counter (1 .. 2 * length - 1)
  best,                 \* best rotation offset (start of lexicographically smallest rotation)
  pc                    \* program counter: which labeled step of the algorithm is active

vars == << string, length, failure, pattern, outer, best, pc >>

Range(seq) == { seq[i] : i \in DOMAIN seq }

TypeInvariant ==
  /\ string \in [0 .. Nat -> CharacterSet]
  /\ length = Len(string)
  /\ failure \in [0 .. 2 * length - 1 -> 0 .. 9]
  /\ pattern \in 0 .. 9
  /\ outer \in 1 .. 2 * length - 1
  /\ best \in 0 .. length - 1
  /\ pc \in {"outer", "lookup", "inner", "update", "follow", "post", "done"}

Init ==
  /\ string \in [0 .. Nat -> CharacterSet]
  /\ length = Len(string)
  /\ failure = [i \in 0 .. 2 * length - 1 |-> Sentinel]
  /\ pattern = Sentinel
  /\ outer = 1
  /\ best = 0
  /\ pc = "outer"

OuterCheck ==
  /\ pc = "outer"
  /\ outer < 2 * length
  /\ pc' = "lookup"
  /\ UNCHANGED << string, length, failure, pattern, outer, best >>

LookupFailure ==
  /\ pc = "lookup"
  /\ pattern' = failure[outer + best]
  /\ pc' = "inner"
  /\ UNCHANGED << string, length, failure, outer, best >>

CharAt(pos) == string[pos % length]

InnerLoop ==
  /\ pc = "inner"
  /\ CharAt(outer) # CharAt(best + pattern)
  /\ pattern # Sentinel
  /\ pc' = "inner"
  /\ UNCHANGED << string, length, failure, pattern, outer, best >>

UpdateBest ==
  /\ pc = "inner"
  /\ CharAt(outer) # CharAt(best + pattern)
  /\ pattern # Sentinel
  /\ CharAt(outer) < CharAt(best + pattern)
  /\ best' = outer
  /\ UNCHANGED << string, length, failure, pattern, outer, pc >>

FollowFailure ==
  /\ pc = "inner"
  /\ CharAt(outer) # CharAt(best + pattern)
  /\ pattern # Sentinel
  /\ pattern' = failure[pattern]
  /\ UNCHANGED << string, length, failure, outer, best, pc >>

PostComparison ==
  /\ pc = "inner"
  /\ CharAt(outer) # CharAt(best + pattern)
  /\ pattern = Sentinel
  /\ IF CharAt(outer) < CharAt(best) THEN best' = outer ELSE best' = best
  /\ failure' = [failure EXCEPT ![outer + best] = IF CharAt(outer) = CharAt(best) THEN 1 ELSE 0]
  /\ pc' = "done"
  /\ UNCHANGED << string, length, pattern, outer >>

Increment ==
  /\ pc = "done"
  /\ outer' = outer + 1
  /\ pc' = "outer"
  /\ UNCHANGED << string, length, failure, pattern, best >>

Done ==
  /\ pc = "done"
  /\ outer >= 2 * length
  /\ UNCHANGED vars

Stall ==
  /\ pc = "done"
  /\ outer >= 2 * length
  /\ UNCHANGED vars

Next == OuterCheck \/ LookupFailure \/ InnerLoop \/ UpdateBest \/ FollowFailure
        \/ PostComparison \/ Increment \/ Done \/ Stall

Spec == Init /\ [][Next]_vars

Terminate == <>(pc = "done")

Correctness ==
  /\ \A i \in 0 .. length - 1 : CharAt(best + i) <= CharAt(i)
  /\ \A i \in 0 .. length - 1 : CharAt(best + i) = CharAt(i) => best <= i

====