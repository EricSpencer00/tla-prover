---- MODULE LeastCircularSubstring ----
EXTENDS Integers, ZSequences, Sequences, FiniteSets, Naturals

CONSTANTS CharacterSet

ASSUME CharacterSet \subseteq Nat

(***************************************************************************)
(* Definitions                                                              *)
(***************************************************************************)

Corpus == ZSeq(CharacterSet)
nil == -1

\* The set of all rotations of a sequence s
Rotations(s) ==
  { [shift |-> i, seq |-> Rotation(s, i)] : i \in 0..Len(s)-1 }

\* Lexicographic preorder on sequences of natural numbers
SeqLexLeq(s, t) ==
  \A i \in 0..(Len(s) - 1) :
    IF i < Len(t) THEN
      IF s[i] < t[i] THEN TRUE
      ELSE IF s[i] = t[i] THEN SeqLexLeq(SubSeq(s, i+1, Len(s)-1),
                                          SubSeq(t, i+1, Len(t)-1))
      ELSE FALSE
    ELSE FALSE

(***************************************************************************)
(* Variables                                                                *)
(***************************************************************************)

VARIABLES b, n, f, i, j, k, pc

vars == << b, n, f, i, j, k, pc >>

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

Init ==
  /\ b \in Corpus
  /\ n = ZLen(b)
  /\ f = [index \in 0..2*n |-> nil]
  /\ i = nil
  /\ j = 1
  /\ k = 0
  /\ pc = "L3"

(***************************************************************************)
(* Actions                                                                  *)
(***************************************************************************)

L3 ==
  /\ pc = "L3"
  /\ IF j < 2 * n
        THEN /\ pc' = "L5"
        ELSE /\ pc' = "Done"
  /\ UNCHANGED << b, n, f, i, j, k >>

L5 ==
  /\ pc = "L5"
  /\ i' = f[j - k - 1]
  /\ pc' = "L6"
  /\ UNCHANGED << b, n, f, j, k >>

L6 ==
  /\ pc = "L6"
  /\ IF b[j % n] /= b[(k + i + 1) % n] /\ i /= nil
        THEN /\ pc' = "L7"
        ELSE /\ pc' = "L10"
  /\ UNCHANGED << b, n, f, i, j, k >>

L7 ==
  /\ pc = "L7"
  /\ IF b[j % n] < b[(k + i + 1) % n]
        THEN /\ pc' = "L8"
        ELSE /\ pc' = "L9"
  /\ UNCHANGED << b, n, f, i, j, k >>

L8 ==
  /\ pc = "L8"
  /\ k' = j - i - 1
  /\ pc' = "L9"
  /\ UNCHANGED << b, n, f, i, j >>

L9 ==
  /\ pc = "L9"
  /\ i' = f[i]
  /\ pc' = "L6"
  /\ UNCHANGED << b, n, f, j, k >>

L10 ==
  /\ pc = "L10"
  /\ IF b[j % n] /= b[(k + i + 1) % n] /\ i = nil
        THEN /\ pc' = "L11"
        ELSE /\ pc' = "L14"
  /\ UNCHANGED << b, n, f, i, j, k >>

L11 ==
  /\ pc = "L11"
  /\ IF b[j % n] < b[(k + i + 1) % n]
        THEN /\ pc' = "L12"
        ELSE /\ pc' = "L13"
  /\ UNCHANGED << b, n, f, i, j, k >>

L12 ==
  /\ pc = "L12"
  /\ k' = j
  /\ pc' = "L13"
  /\ UNCHANGED << b, n, f, i, j >>

L13 ==
  /\ pc = "L13"
  /\ f' = [f EXCEPT ![j - k] = nil]
  /\ pc' = "LVR"
  /\ UNCHANGED << b, n, i, j, k >>

L14 ==
  /\ pc = "L14"
  /\ f' = [f EXCEPT ![j - k] = i + 1]
  /\ pc' = "LVR"
  /\ UNCHANGED << b, n, i, j, k >>

LVR ==
  /\ pc = "LVR"
  /\ j' = j + 1
  /\ pc' = "L3"
  /\ UNCHANGED << b, n, f, i, k >>

Terminating ==
  pc = "Done" /\ UNCHANGED vars

Next ==
  L3 \/ L5 \/ L6 \/ L7 \/ L8 \/ L9 \/ L10 \/ L11 \/ L12 \/ L13 \/ L14 \/ LVR \/ Terminating

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Type invariant (kept for debugging, not used for safety)               *)
(***************************************************************************)

TypeOK ==
  /\ b \in Corpus
  /\ n = ZLen(b)
  /\ f \in [0..2*n -> 0..2*n \cup {nil}]
  /\ i \in 0..2*n \cup {nil}
  /\ j \in 0..2*n \cup {1}
  /\ k \in 0..(n-1) \cup {0}

(***************************************************************************)
(* Correctness property                                                    *)
(***************************************************************************)

IsLeastMinimalRotation(s, r) ==
  LET rotation == Rotation(s, r) IN
    /\ \A other \in Rotations(s) :
        rotation \preceq other.seq
    /\ rotation = other.seq => (r <= other.shift)

Correctness ==
  pc = "Done" => IsLeastMinimalRotation(b, k)

=============================================================================