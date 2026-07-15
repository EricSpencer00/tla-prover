---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS CharacterSet, Nat

(* ---------- Helper definitions ---------- *)

\* The sentinel value for undefined failure-function entries and pattern index.
Sentinel == -1

(* Index modulo a positive length, returning a natural number in 0..len-1 *)
Mod(i, len) == i % len

(* ---------- State variables ---------- *)

VARIABLES
    input,          \* The input string, a sequence of characters
    n,              \* Length of the input string
    failure,        \* Failure function array, indexed 0..2*n-1
    patIdx,         \* Current pattern‑match index (or Sentinel)
    i,              \* Outer loop counter, ranging 1..2*n
    best,           \* Current best rotation offset, 0..n-1
    pc              \* Program counter indicating the current labeled step

(* ---------- Initialization ---------- *)

Init ==
    /\ input \in Seq(CharacterSet)               \* any finite sequence over the alphabet
    /\ n = Len(input)
    /\ n >= 0
    /\ failure = [j \in 0..2*n-1 |-> Sentinel]    \* all entries undefined
    /\ patIdx = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterLoopCheck"

(* ---------- Actions (labeled steps) ---------- *)

OuterLoopCheck ==
    /\ pc = "OuterLoopCheck"
    /\ IF i >= 2*n
          THEN /\ pc' = "Terminated"
                /\ UNCHANGED <<input, n, failure, patIdx, i, best>>
          ELSE /\ pc' = "FailureLookup"
                /\ UNCHANGED <<input, n, failure, patIdx, i, best>>

FailureLookup ==
    /\ pc = "FailureLookup"
    /\ patIdx' = failure[Mod(i + best, n)]          \* lookup failure entry for the current offset
    /\ pc' = "InnerCompare"
    /\ UNCHANGED <<input, n, failure, i, best>>

InnerCompare ==
    /\ pc = "InnerCompare"
    /\ IF patIdx # Sentinel /\ input[Mod(i + best, n)] = input[Mod(patIdx + 1, n)]
          THEN /\ patIdx' = patIdx + 1
                /\ pc' = "InnerCompare"          \* stay in inner compare, advance patIdx
                /\ UNCHANGED <<input, n, failure, i, best>>
          ELSE /\ pc' = "PostComparison"
                /\ UNCHANGED <<input, n, failure, patIdx, i, best>>

PostComparison ==
    /\ pc = "PostComparison"
    /\ IF patIdx # Sentinel /\ input[Mod(i + best, n)] # input[Mod(patIdx + 1, n)]
          THEN /\ IF input[Mod(i + best, n)] < input[Mod(patIdx + 1, n)]
                    THEN best' = i
                    ELSE UNCHANGED best
                /\ failure' = [failure EXCEPT ![Mod(i + best, n)] = IF input[Mod(i + best, n)] # input[Mod(patIdx + 1, n)]
                                                                      THEN Sentinel
                                                                      ELSE patIdx + 2]
                /\ patIdx' = Sentinel
                /\ pc' = "Increment"
                /\ UNCHANGED <<input, n, i>>
          ELSE /\ IF patIdx = Sentinel
                    THEN /\ IF input[Mod(i + best, n)] < input[Mod(i, n)]
                              THEN best' = i
                              ELSE UNCHANGED best
                          /\ failure' = [failure EXCEPT ![Mod(i + best, n)] = 0]
                    ELSE /\ failure' = failure
                /\ patIdx' = Sentinel
                /\ pc' = "Increment"
                /\ UNCHANGED <<input, n, i, best>>

Increment ==
    /\ pc = "Increment"
    /\ i' = i + 1
    /\ pc' = "OuterLoopCheck"
    /\ UNCHANGED <<input, n, failure, patIdx, best>>

Stutter ==
    /\ pc = "Terminated"
    /\ UNCHANGED <<input, n, failure, patIdx, i, best, pc>>

Next ==
    \/ OuterLoopCheck
    \/ FailureLookup
    \/ InnerCompare
    \/ PostComparison
    \/ Increment
    \/ Stutter

(* ---------- Specification ---------- *)

Spec == Init /\ [][Next]_<<input, n, failure, patIdx, i, best, pc>>

(* ---------- Type invariant (state‑level) ---------- *)

TypeInvariant ==
    /\ input \in Seq(CharacterSet)
    /\ n = Len(input)
    /\ failure \in [0..2*n-1 -> (0..2*n-1) \cup {Sentinel}]
    /\ patIdx \in (0..2*n-1) \cup {Sentinel}
    /\ i \in 1..2*n
    /\ best \in 0..n-1
    /\ pc \in {"OuterLoopCheck", "FailureLookup", "InnerCompare",
               "PostComparison", "Increment", "Terminated"}

(* ---------- Correctness invariant ---------- *)

\* Helper: rotation of a sequence by offset k
Rotate(seq, k) == seq \o seq'                  \* concatenates seq with itself
\* Actually we only need the first n characters after starting at k
Rotated(seq, k) == SubSeq( seq \o seq, k + 1, k + n )

Correctness ==
    /\ pc = "Terminated"
    /\ \A j \in 0..n-1 :
          LexicographicOrder( Rotated(input, best), Rotated(input, j) ) <= 0

(* Lexicographic order of two sequences of equal length, returning -1,0,1 *)
LexicographicOrder(s, t) ==
    IF s = t THEN 0 ELSE
    IF \E k \in 1..Len(s) : s[k] # t[k] THEN
        IF s[Min({k \in 1..Len(s) : s[k] # t[k]})] < t[Min({k \in 1..Len(s) : s[k] # t[k]})] THEN -1 ELSE 1
    ELSE 0

====