---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS CharacterSet, Nat

(* ------------------------------------------------------------------- *)
(*  Helper definitions                                                *)
(* ------------------------------------------------------------------- *)

\* The sentinel value used in the failure function and pattern index.
\* It must be outside the range of valid indices 0..2*len-1.
Sentinel == -1

\* Modulo operation that works for natural numbers (avoid negative modulo).
Mod(i, m) == IF m = 0 THEN 0 ELSE i % m

(* ------------------------------------------------------------------- *)
(*  Variables                                                         *)
(* ------------------------------------------------------------------- *)

VARIABLES
    str,        \* Input string: a sequence of characters (elements of CharacterSet)
    len,        \* Length of the input string
    fail,       \* Failure function: array indexed 0..2*len-1, values in -1..2*len-1
    pat,        \* Pattern-match index, value in -1..2*len-1
    i,          \* Outer loop counter, ranges from 1..2*len
    offset      \* Best rotation offset found so far, in 0..len-1

vars == << str, len, fail, pat, i, offset >>

(* ------------------------------------------------------------------- *)
(*  Type definitions                                                  *)
(* ------------------------------------------------------------------- *)

TypeOK ==
    /\ str \in Seq(CharacterSet)
    /\ len = Len(str)
    /\ offset \in 0..len-1
    /\ i \in 1..2*len
    /\ fail \in [0..2*len-1 -> {-1} \cup 0..2*len-1]
    /\ pat \in {-1} \cup 0..2*len-1

(* ------------------------------------------------------------------- *)
(*  Initial state                                                     *)
(* ------------------------------------------------------------------- *)

Init ==
    /\ str \in Seq(CharacterSet)
    /\ len = Len(str)
    /\ offset = 0
    /\ i = 1
    /\ pat = Sentinel
    /\ fail = [j \in 0..2*len-1 |-> Sentinel]

(* ------------------------------------------------------------------- *)
(*  Actions                                                           *)
(* ------------------------------------------------------------------- *)

OuterLoopContinue ==
    /\ i < 2*len
    /\ UNCHANGED << str, len, offset >>

FailureLookup ==
    /\ TRUE
    /\ pat' = fail[ i - offset ]
    /\ UNCHANGED << str, len, fail, i, offset >>

InnerCompareLoop ==
    /\ i < 2*len
    /\ LET
          ci == str[ Mod(i, len) + 1 ]               \* character at current position
          cj == str[ Mod(pat, len) + 1 ]             \* character at candidate position
       IN
          IF ci = cj THEN
              /\ pat' = pat + 1
              /\ UNCHANGED << str, len, fail, i, offset >>
          ELSE
              /\ pat' = Sentinel
              /\ UNCHANGED << str, len, fail, i, offset >>

UpdateOffsetLess ==
    /\ i < 2*len
    /\ LET
          ci == str[ Mod(i, len) + 1 ]
          cj == str[ Mod(pat, len) + 1 ]
       IN
          /\ ci < cj
          /\ offset' = (i - pat) % len
          /\ UNCHANGED << str, len, fail, pat, i >>

PostComparison ==
    /\ i < 2*len
    /\ LET
          ci == str[ Mod(i, len) + 1 ]
          cj == str[ Mod(pat, len) + 1 ]
       IN
          IF ci # cj /\ pat = Sentinel THEN
              /\ IF ci < cj THEN offset' = i % len ELSE UNCHANGED offset
              /\ fail' = [fail EXCEPT ![i - offset] = IF ci < cj THEN i % len ELSE Sentinel]
              /\ UNCHANGED << str, len, pat, i >>
          ELSE
              /\ UNCHANGED << str, len, pat, i, offset, fail >>

IncI ==
    /\ i < 2*len
    /\ i' = i + 1
    /\ UNCHANGED << str, len, fail, pat, offset >>

Terminate ==
    /\ i >= 2*len
    /\ UNCHANGED vars

Stutter ==
    /\ UNCHANGED vars

Next ==
    \/ OuterLoopContinue
    \/ FailureLookup
    \/ InnerCompareLoop
    \/ UpdateOffsetLess
    \/ PostComparison
    \/ IncI
    \/ Terminate
    \/ Stutter

(* ------------------------------------------------------------------- *)
(*  Specification                                                     *)
(* ------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------- *)
(*  Invariants                                                        *)
(* ------------------------------------------------------------------- *)

TypeInvariant == TypeOK

(* Correctness: the rotation starting at 'offset' is lexicographically minimal *)
Correctness ==
    /\ offset \in 0..len-1
    /\ \A j \in 0..len-1 :
          LET rotOff == SubSeq(str, offset+1, len) \o SubSeq(str, 1, offset)
              rotJ   == SubSeq(str, j+1, len) \o SubSeq(str, 1, j)
           IN rotOff <= rotJ   \* lexical order on sequences

=============================================================================