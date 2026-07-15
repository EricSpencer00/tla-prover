---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANTS
    CharacterSet, \* finite set of characters (subset of Nat)
    Nat          \* the set of natural numbers (used for sentinel)

(*--------------------------------------------------------------------
  Definitions
--------------------------------------------------------------------*)

(* sentinel value for "undefined" entries in Failure and for PatternIdx *)
Sentinel == -1

VARIABLES
    str,        \* the input string, a sequence of characters
    n,          \* length of str
    Failure,    \* failure function: array indexed 0..2*n-1
    PatternIdx, \* current pattern-match index (or Sentinel)
    i,          \* outer loop counter, runs from 1 to 2*n
    k,          \* current best rotation offset (0..n-1)
    pc          \* program counter indicating the current step

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)

CharInSet(c) == c \in CharacterSet

StrInSet(s) == /\ Len(s) = n
               /\ \A j \in 0..n-1: CharInSet(s[j])

FailInRange(f) == /\ DOMAIN f = 0..2*n-1
                  /\ \A j \in DOMAIN f:
                        f[j] = Sentinel \/ (0 <= f[j] /\ f[j] <= n)

TypeOK ==
    /\ StrInSet(str)
    /\ n = Len(str)
    /\ FailInRange(Failure)
    /\ (PatternIdx = Sentinel \/ (0 <= PatternIdx /\ PatternIdx <= n))
    /\ (1 <= i /\ i <= 2*n+1)   \* i may be 2*n+1 after termination
    /\ (0 <= k /\ k < n)
    /\ pc \in {"OuterLoopCheck", "FailureLookup", "InnerCmp", 
                "UpdateBest", "FollowFailure", "PostComparison",
                "IncCounter", "Done"}

(* character at position p of the doubled string, modulo n *)
CharAt(p) == str[p % n]

(* rotation starting at offset off *)
Rotation(off) == << CharAt(off + j) : j \in 0..n-1 >>

(* lexicographic less-or-equal for two rotations *)
Leq(off1, off2) ==
    \A j \in 0..n-1: Rotation(off1)[j] <= Rotation(off2)[j]

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)

Init ==
    /\ \E s \in Seq(CharacterSet):
          /\ Len(s) = n
          /\ str = s
    /\ n = Len(str)
    /\ Failure = [j \in 0..2*n-1 |-> Sentinel]
    /\ PatternIdx = Sentinel
    /\ i = 1
    /\ k = 0
    /\ pc = "OuterLoopCheck"
    /\ TypeOK

(*--------------------------------------------------------------------
  Actions corresponding to each program counter label
--------------------------------------------------------------------*)
OuterLoopCheck ==
    /\ pc = "OuterLoopCheck"
    /\ IF i > 2 * n
          THEN /\ pc' = "Done"
               /\ UNCHANGED << str, n, Failure, PatternIdx, i, k >>
          ELSE /\ pc' = "FailureLookup"
               /\ UNCHANGED << str, n, Failure, PatternIdx, i, k >>

FailureLookup ==
    /\ pc = "FailureLookup"
    /\ pc' = "InnerCmp"
    /\ UNCHANGED << str, n, Failure, PatternIdx, i, k >>

InnerCmp ==
    /\ pc = "InnerCmp"
    /\ LET curPos == i - 1 IN
       IF CharAt(curPos) /= CharAt(k + PatternIdx)
          THEN IF PatternIdx # Sentinel
                  THEN /\ pc' = "FollowFailure"
                       /\ UNCHANGED << str, n, Failure, PatternIdx, i, k >>
                  ELSE /\ pc' = "PostComparison"
                       /\ UNCHANGED << str, n, Failure, PatternIdx, i, k >>
          ELSE /\ PatternIdx' = PatternIdx + 1
               /\ pc' = "InnerCmp"
               /\ UNCHANGED << str, n, Failure, i, k >>

UpdateBest ==
    /\ pc = "UpdateBest"
    /\ k' = i - PatternIdx - 1
    /\ pc' = "FollowFailure"
    /\ UNCHANGED << str, n, Failure, PatternIdx, i >>

FollowFailure ==
    /\ pc = "FollowFailure"
    /\ PatternIdx' = Failure[i - 1]
    /\ pc' = "InnerCmp"
    /\ UNCHANGED << str, n, Failure, i, k >>

PostComparison ==
    /\ pc = "PostComparison"
    /\ LET curPos == i - 1 IN
       IF CharAt(curPos) < CharAt(k + PatternIdx)
          THEN /\ k' = i - PatternIdx - 1
          ELSE UNCHANGED k
    /\ IF PatternIdx = Sentinel
          THEN Failure' = [Failure EXCEPT ![i - 1] = Sentinel]
          ELSE Failure' = [Failure EXCEPT ![i - 1] = PatternIdx + 1]
    /\ pc' = "IncCounter"
    /\ UNCHANGED << str, n, PatternIdx, i >>

IncCounter ==
    /\ pc = "IncCounter"
    /\ i' = i + 1
    /\ pc' = "OuterLoopCheck"
    /\ UNCHANGED << str, n, Failure, PatternIdx, k >>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED << str, n, Failure, PatternIdx, i, k, pc >>

Next ==
    \/ OuterLoopCheck
    \/ FailureLookup
    \/ InnerCmp
    \/ UpdateBest
    \/ FollowFailure
    \/ PostComparison
    \/ IncCounter
    \/ Done

Spec == Init /\ [][Next]_<<str, n, Failure, PatternIdx, i, k, pc>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)

TypeInvariant == TypeOK

(* Correctness: k points to a rotation that is <= every other rotation *)
Correctness ==
    /\ k \in 0..n-1
    /\ \A off \in 0..n-1: Leq(k, off)

====