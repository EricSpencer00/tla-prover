---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  CharacterSet,
  Nat

Cap == 2

Sentinel == Cap

VARIABLES
  input,
  length,
  failFunc,
  matchIdx,
  i,
  best,
  pc

vars == <<input, length, failFunc, matchIdx, i, best, pc>>

\* Zero-indexed version of the input (required by the spec's indexing).
InputCorpus == UNION { [1..n -> CharacterSet] : n \in Nat }

TypeInvariant ==
  /\ input \in InputCorpus
  /\ length = Len(input)
  /\ failFunc \in [0..(2 * length) -> 0..Cap]
  /\ matchIdx \in 0..Cap
  /\ i \in 0..(2 * length)
  /\ best \in 0..(length - 1)
  /\ pc \in {"outer", "lookup", "inner", "postcompare", "done"}

\* A rotation is the original string with a cyclic shift by k positions.
Rotate(s, k) == << s[((j + k) % Len(s)) + 1] : j \in 0..(Len(s) - 1) >>

LexMinRotation ==
  \A n \in 0..(length - 1) :
    /\ Len(input) > 0
    /\ Rotate(input, best) =< Rotate(input, n)
    /\ (Rotate(input, best) = Rotate(input, n) => best =< n)

Init ==
  /\ \E w \in InputCorpus : input = w
  /\ length = Len(input)
  /\ failFunc = [k \in 0..(2 * length) |-> Sentinel]
  /\ matchIdx = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "outer"

OuterLoop ==
  /\ pc = "outer"
  /\ i < (2 * length)
  /\ pc' = "lookup"
  /\ UNCHANGED <<input, length, failFunc, matchIdx, i, best>>

FailureLookup ==
  /\ pc = "lookup"
  /\ matchIdx' = failFunc[(i - 1) - best]
  /\ pc' = "inner"
  /\ UNCHANGED <<input, length, failFunc, i, best>>

\* The inner loop carries the failure-function state forward as a
\* single-valued index, so it is a deterministic comparison chain, not
\* a branching one -- that is what keeps the model finite.
InnerCompare ==
  /\ pc = "inner"
  /\ LET a == input[((i % length) + 1)]
         b == input[((((i - matchIdx - 1) % length) + 1) + 1)]
     IN IF \/ a = b
           \/ (matchIdx = Sentinel /\ a /= b)
           THEN pc' = "postcompare" /\ UNCHANGED matchIdx
           ELSE /\ matchIdx' = failFunc[matchIdx]
                /\ pc' = "inner"
  /\ UNCHANGED <<input, length, failFunc, i, best>>

UpdateBest ==
  /\ pc = "postcompare"
  /\ LET a == input[((i % length) + 1)]
         b == input[(((((i - matchIdx - 1) % length) + 1) + 1))]
     IN IF a < b
          THEN best' = i
          ELSE UNCHANGED best
  /\ UNCHANGED <<input, length, matchIdx, i>>

FollowFail ==
  /\ pc = "postcompare"
  /\ matchIdx' = IF matchIdx = Sentinel THEN Sentinel ELSE matchIdx + 1
  /\ failFunc' = [failFunc EXCEPT ![(i - 1) - best] = matchIdx]
  /\ pc' = "outer"
  /\ i' = i + 1
  /\ UNCHANGED <<input, length, best>>

Done ==
  /\ pc = "outer"
  /\ i >= (2 * length)
  /\ pc' = "done"
  /\ UNCHANGED <<input, length, failFunc, matchIdx, i, best>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop
  \/ FailureLookup
  \/ InnerCompare
  \/ UpdateBest
  \/ FollowFail
  \/ Done
  \/ Stall

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "done")

====