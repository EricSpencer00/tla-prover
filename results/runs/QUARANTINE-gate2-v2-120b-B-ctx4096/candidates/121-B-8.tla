---- MODULE LeastCircularSubstring ----
EXTENDS Integers, ZSequences, FiniteSets, Sequences

CONSTANTS CharacterSet

ASSUME CharacterSet \subseteq Nat

\* Define the character nil and the corpus type
Corpus == ZSeq(CharacterSet)
nil == -1

VARIABLES b, n, f, i, j, k, pc

(* ------------------------------------------------------------------------ *)
(* Initialization ---------------------------------------------------------- *)
Init ==
    /\ b \in Corpus
    /\ n = ZLen(b)
    /\ f = [index \in 0..2*n |-> nil]
    /\ i = nil
    /\ j = 1
    /\ k = 0
    /\ pc = "L3"

(* ------------------------------------------------------------------------ *)
(* Action definitions ------------------------------------------------------ *)

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
    /\ pc = "Done"
    /\ UNCHANGED << b, n, f, i, j, k, pc >>

Next ==
    L3 \/ L5 \/ L6 \/ L7 \/ L8 \/ L9 \/ L10 \/ L11 \/ L12 \/ L13 \/ L14 \/ LVR \/ Terminating

(* ------------------------------------------------------------------------ *)
(* Specification ----------------------------------------------------------- *)

Spec ==
    Init /\ [][Next]_<<b, n, f, i, j, k, pc>>

Termination ==
    <> (pc = "Done")

(* ------------------------------------------------------------------------ *)
(* Types ------------------------------------------------------------------- *)

TypeInvariant ==
    /\ b \in Corpus
    /\ n = ZLen(b)
    /\ f \in [0..2*n -> 0..2*n \cup {nil}]
    /\ i \in 0..2*n \cup {nil}
    /\ j \in 0..2*n \cup {1}
    /\ k \in 0..n

(* ------------------------------------------------------------------------ *)
(* Correctness ------------------------------------------------------------- *)

\* Rotation of a sequence s by shift r (0 ≤ r < Len(s))
Rotation(s, r) ==
    LET len == Len(s) IN
    IF len = 0 THEN <<>>
    ELSE
        LET idx == r % len IN
        s[idx .. len-1] \o s[0 .. idx-1]

\* Set of all rotations of s, each paired with its shift
Rotations(s) ==
    { <<seq |-> Rotation(s, r), shift |-> r>> : r \in 0..Len(s)-1 }

\* Predicate stating that rotation r of b is lexicographically minimal
IsLeastMinimalRotation(b, r) ==
    LET rot == Rotation(b, r) IN
    \A other \in Rotations(b) :
        rot \preceq other.seq
        /\ (rot = other.seq => r <= other.shift)

Correctness ==
    pc = "Done" => IsLeastMinimalRotation(b, k)

=================================