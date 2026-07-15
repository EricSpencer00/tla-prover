------------------------------ MODULE LeastCircularSubstring ------------------------------
EXTENDS Integers, ZSequences

CONSTANTS CharacterSet

ASSUME CharacterSet \subseteq Nat

(***************************************************************************)
(* Translation of Booth's lexicographically-least circular substring      *)
(* algorithm (1980) into PlusCal/TLA+. The translation follows the original *)
(* algorithm closely; only the PlusCal control‑flow variable `pc` is added. *)
(***************************************************************************)

VARIABLES b, n, f, i, j, k, pc

(* ------------------------------------------------------------------------ *)
(* Definitions used both in the algorithm and in the invariant               *)
Corpus == ZSeq(CharacterSet)
nil    == -1

(* ------------------------------------------------------------------------ *)
(* Initial state                                                            *)
Init ==
    /\ b \in Corpus
    /\ n = ZLen(b)
    /\ f = [index \in 0..2*n |-> nil]
    /\ i = nil
    /\ j = 1
    /\ k = 0
    /\ pc = "L3"

(* ------------------------------------------------------------------------ *)
(* Control‑flow actions produced by the PlusCal translation                 *)

L3 ==
    /\ pc = "L3"
    /\ IF j < 2 * n
          THEN pc' = "L5"
          ELSE pc' = "Done"
    /\ UNCHANGED << b, n, f, i, j, k >>

L5 ==
    /\ pc = "L5"
    /\ i' = f[j - k - 1]
    /\ pc' = "L6"
    /\ UNCHANGED << b, n, f, j, k >>

L6 ==
    /\ pc = "L6"
    /\ IF b[j % n] /= b[(k + i + 1) % n] /\ i /= nil
          THEN pc' = "L7"
          ELSE pc' = "L10"
    /\ UNCHANGED << b, n, f, i, j, k >>

L7 ==
    /\ pc = "L7"
    /\ IF b[j % n] < b[(k + i + 1) % n]
          THEN pc' = "L8"
          ELSE pc' = "L9"
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
          THEN pc' = "L11"
          ELSE pc' = "L14"
    /\ UNCHANGED << b, n, f, i, j, k >>

L11 ==
    /\ pc = "L11"
    /\ IF b[j % n] < b[(k + i + 1) % n]
          THEN pc' = "L12"
          ELSE pc' = "L13"
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
(* Full specification                                                       *)
Spec == Init /\ [][Next]_<<b, n, f, i, j, k, pc>>

Termination == <> (pc = "Done")

(* ------------------------------------------------------------------------ *)
(* Type invariant (helps TLC, does not weaken correctness)                 *)
TypeInv ==
    /\ b \in Corpus
    /\ n = ZLen(b)
    /\ f \in [0..2*n -> 0..2*n \cup {nil}]
    /\ i \in 0..2*n \cup {nil}
    /\ j \in 0..2*n \cup {1}
    /\ k \in 0..2*n

(* ------------------------------------------------------------------------ *)
(* Correctness property – the algorithm returns the lexicographically   *)
(* minimal rotation of the input string `b`.                                *)

IsLeastMinimalRotation(s, r) ==
    LET rotation == Rotation(s, r) IN
    /\ \A other \in Rotations(s) :
          rotation \preceq other.seq
    /\ rotation = other.seq => r <= other.shift

Correctness ==
    /\ pc = "Done"
    /\ IsLeastMinimalRotation(b, k)

=============================================================================