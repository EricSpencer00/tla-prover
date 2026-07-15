---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

(* ----------------------------------------------------------------------
   Constants (set in the .cfg)
   ---------------------------------------------------------------------- *)
CONSTANT CharacterSet
CONSTANT Nat

(* ----------------------------------------------------------------------
   Derived constants
   ---------------------------------------------------------------------- *)
Sentinel == -1               \* sentinel value indicating "undefined"

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES
    s,              \* input string (sequence of characters, zero-indexed)
    n,              \* length of s
    f,              \* failure function, array indexed 0..2*n
    k,              \* pattern-match index (current failure link)
    i,              \* outer loop counter, 1..2*n
    offset,         \* best rotation offset found so far, 0..n-1
    pc              \* program counter (label of the current step)

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
CharSeq(seq) == 
    /\ seq \in Seq(CharacterSet)
    /\ Len(seq) >= 1

IdxInSeq(idx) == idx \in 0..(n-1)

CharAt(pos) == s[(pos % n) + 1]   \* +1 because Sequences are 1-indexed in TLA+

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ \E seq \in Seq(CharacterSet) :
          /\ Len(seq) >= 1
          /\ s = seq
    /\ n = Len(s)
    /\ f = [j \in 0..(2*n) |-> Sentinel]
    /\ k = Sentinel
    /\ i = 1
    /\ offset = 0
    /\ pc = "OuterCheck"

(* ----------------------------------------------------------------------
   Actions (labeled by the program counter)
   ---------------------------------------------------------------------- *)

OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i < 2 * n
          THEN /\ pc' = "FailureLookup"
          ELSE /\ pc' = "Done"
    /\ UNCHANGED <<s, n, f, k, i, offset>>

FailureLookup ==
    /\ pc = "FailureLookup"
    /\ let j == (i - offset) % n in
       /\ k' = f[j]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<s, n, f, i, offset>>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ IF s[(i % n) + 1] # s[( (i - offset) % n) + 1]
          THEN 
               IF k # Sentinel
                  THEN /\ pc' = "FollowFailure"
                  ELSE /\ pc' = "PostComparison"
          ELSE
               /\ pc' = "FollowFailure"
    /\ UNCHANGED <<s, n, f, i, offset, k>>

FollowFailure ==
    /\ pc = "FollowFailure"
    /\ IF k = Sentinel
          THEN /\ pc' = "PostComparison"
          ELSE /\ k' = f[k]
               /\ pc' = "FollowFailure"
    /\ UNCHANGED <<s, n, f, i, offset>>

PostComparison ==
    /\ pc = "PostComparison"
    /\ LET cur  == s[(i % n) + 1]
           cand == s[( (i - offset) % n) + 1] IN
       /\ IF cur # cand
             THEN /\ IF cur < cand
                       THEN offset' = i % n
                       ELSE UNCHANGED offset
                  /\ f' = IF cur < cand
                            THEN [f EXCEPT ![ (i - offset) % n ] = Sentinel]
                            ELSE [f EXCEPT ![ (i - offset) % n ] = 
                                   IF k = Sentinel THEN 0 ELSE k + 1]
             ELSE UNCHANGED <<offset, f>>
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<s, n, k>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<s, n, f, k, i, offset, pc>>

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<s, n, f, k, i, offset, pc>>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ OuterCheck
    \/ FailureLookup
    \/ InnerLoop
    \/ FollowFailure
    \/ PostComparison
    \/ Done
    \/ Stutter

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<s, n, f, k, i, offset, pc>>

(* ----------------------------------------------------------------------
   Type invariant (ensures all variables stay within their intended domains)
   ---------------------------------------------------------------------- *)
TypeInvariant ==
    /\ s \in Seq(CharacterSet)
    /\ n = Len(s) /\ n >= 1
    /\ f \in [0..(2*n) -> (Sentinel \cup 0..(n-1))]
    /\ k \in Sentinel \cup 0..(n-1)
    /\ i \in 1..(2*n + 1)   \* i may be 2*n+1 after the last increment
    /\ offset \in 0..(n-1)
    /\ pc \in {"OuterCheck", "FailureLookup", "InnerLoop",
               "FollowFailure", "PostComparison", "Done"}

(* ----------------------------------------------------------------------
   Correctness invariant (lexicographically minimal rotation)
   ---------------------------------------------------------------------- *)
Correctness ==
    \A shift \in 0..(n-1) :
        LET rotOff   == offset
            rotShift == shift IN
        LexLessOrEqual(offToString(rotOff), offToString(rotShift))

(* Helper to convert a rotation offset into the corresponding string *)
offToString(off) ==
    [j \in 1..n |-> s[((off + j - 1) % n) + 1]]

(* Lexicographic comparison of two strings represented as functions 1..n -> CharSet *)
LexLessOrEqual(str1, str2) ==
    \A j \in 1..n :
        IF str1[j] # str2[j] THEN str1[j] < str2[j] ELSE TRUE

(* ----------------------------------------------------------------------
   Liveness (termination) property – not required as an identifier but
   useful for completeness; can be omitted from the final .cfg.
   ---------------------------------------------------------------------- *)
Termination == <>[](pc = "Done")

=============================================================================