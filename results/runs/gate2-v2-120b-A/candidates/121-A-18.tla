---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

(* ----------------------------------------------------------------------
   Constants
   ---------------------------------------------------------------------- *)
CONSTANTS CharacterSet, Nat

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES
    str,            \* input string: a sequence of characters from CharacterSet
    n,              \* length of the input string
    fail,           \* failure function array indexed from 0 to 2*n
    patIdx,         \* pattern-match index (corresponds to "j" in many presentations)
    i,              \* outer loop counter
    best,           \* best rotation offset found so far
    pc              \* program counter (labels the current step)

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
Sentinel == -1                         \* sentinel value for "undefined"

Rot(s, off) ==                              \* rotation of sequence s by offset off
    IF off = 0 THEN s
    ELSE << >> @@ s[off .. Len(s)-1] @@ s[1 .. off]

CharAt(idx) == str[(idx % n) + 1]        \* 1‑based indexing for sequences

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ str \in [1..Nat -> CharacterSet]        \* nondeterministically chosen string, bounded by Nat
    /\ n = Len(str)                           \* length of the chosen string
    /\ n > 0                                   \* non‑empty string (algorithm assumes at least one character)
    /\ fail = [j \in 0..(2*n) |-> Sentinel]   \* failure function initialized to sentinel
    /\ patIdx = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterLoopCheck"

(* ----------------------------------------------------------------------
   Actions (one per labeled step)
   ---------------------------------------------------------------------- *)

(* 1. Outer loop check *)
OuterLoopCheck ==
    /\ pc = "OuterLoopCheck"
    /\ IF i < 2*n
          THEN /\ pc' = "FailureLookup"
               /\ UNCHANGED <<str, n, fail, patIdx, i, best>>
          ELSE /\ pc' = "Done"
               /\ UNCHANGED <<str, n, fail, patIdx, i, best, fail, patIdx>>

(* 2. Failure function lookup (no state change, just move to comparison) *)
FailureLookup ==
    /\ pc = "FailureLookup"
    /\ pc' = "InnerComparison"
    /\ UNCHANGED <<str, n, fail, patIdx, i, best, i>>

(* 3. Inner comparison loop - may iterate multiple times *)
InnerComparison ==
    /\ pc = "InnerComparison"
    /\ LET cur == CharAt(i)
           cand == CharAt(best + i - patIdx) IN
       IF cur = cand
          THEN /\ patIdx' = i
               /\ pc' = "FollowFailure"
               /\ UNCHANGED <<str, n, fail, i, best>>
          ELSE IF cur < cand
               THEN /\ best' = (i - patIdx) % n
                    /\ patIdx' = i
                    /\ pc' = "FollowFailure"
                    /\ UNCHANGED <<str, n, fail, i>>
               ELSE IF patIdx # Sentinel
                    THEN /\ patIdx' = fail[patIdx]
                         /\ pc' = "InnerComparison"
                         /\ UNCHANGED <<str, n, fail, i, best>>
                    ELSE /\ (* cur > cand and patIdx = Sentinel *)
                         pc' = "PostComparison"
                         /\ UNCHANGED <<str, n, fail, i, best, patIdx>>

(* 4. Follow failure function chain after successful match or update *)
FollowFailure ==
    /\ pc = "FollowFailure"
    /\ pc' = "PostComparison"
    /\ UNCHANGED <<str, n, fail, patIdx, i, best>>

(* 5. Post‑comparison handling *)
PostComparison ==
    /\ pc = "PostComparison"
    /\ LET cur == CharAt(i)
           cand == CharAt(best + i - patIdx) IN
       IF cur # cand /\ patIdx = Sentinel
          THEN /\ IF cur < cand
                     THEN best' = (i - patIdx) % n
                     ELSE UNCHANGED best
               /\ fail' = [fail EXCEPT ![i] = IF cur = cand THEN Sentinel ELSE i + 1]
               /\ pc' = "Increment"
               /\ UNCHANGED <<str, n, patIdx, i>>
          ELSE /\ UNCHANGED <<str, n, fail, patIdx, i, best>>
               /\ pc' = "Increment"

(* 6. Increment loop counter *)
Increment ==
    /\ pc = "Increment"
    /\ i' = i + 1
    /\ pc' = "OuterLoopCheck"
    /\ UNCHANGED <<str, n, fail, patIdx, best>>

(* 7. Stuttering after termination *)
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, n, fail, patIdx, i, best, pc>>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ OuterLoopCheck
    \/ FailureLookup
    \/ InnerComparison
    \/ FollowFailure
    \/ PostComparison
    \/ Increment
    \/ Stutter

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<str, n, fail, patIdx, i, best, pc>>

(* ----------------------------------------------------------------------
   Safety property: type invariant
   ---------------------------------------------------------------------- *)
TypeInvariant ==
    /\ str \in [1..Nat -> CharacterSet]
    /\ n = Len(str)
    /\ n > 0
    /\ fail \in [0..2*n -> (0..2*n) \cup {Sentinel}]
    /\ patIdx \in (0..2*n) \cup {Sentinel}
    /\ i \in 1..(2*n + 1)               \* i may be 2*n after the last increment
    /\ best \in 0..(n-1)
    /\ pc \in {"OuterLoopCheck","FailureLookup","InnerComparison",
               "FollowFailure","PostComparison","Increment","Done"}

(* ----------------------------------------------------------------------
   Correctness: lexicographically‑least rotation
   ---------------------------------------------------------------------- *)
Correctness ==
    /\ pc = "Done"
    /\ \A off \in 0..(n-1) :
           Rot(str, best) <= Rot(str, off)

=============================================================================