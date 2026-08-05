---- MODULE LeastCircularSubstring ----
(* An implementation of the lexicographically-least circular substring algorithm
   from Booth's 1980 paper (see https://doi.org/10.1016/0020-0190(80)90149-0). *)
EXTENDS Integers, ZSequences

CONSTANTS CharacterSet

ASSUME CharacterSet \subseteq Nat

(* define statement *)
Corpus == ZSeq(CharacterSet)
nil == -1

VARIABLES b, n, f, i, j, k, pc
vars == << b, n, f, i, j, k, pc >>

\* Many algorithmic steps are synchronized into a single control step here; that
\* is to say "pc = L10" and the L10 case in the Next relation are not
\* disjoint.  The TLC error is that a case is reachable which leaves pc null
\* rather than assigning it, so every case of the L10 kind must set pc.

Init ==
  /\ b \in Corpus /\ n = ZLen(b)
  /\ f = [index \in 0..2*n |-> nil]
  /\ i = nil /\ j = 1 /\ k = 0 /\ pc = "L3"

L3 ==
  /\ pc = "L3"
  /\ IF j < 2 * n THEN pc' = "L5" ELSE pc' = "Done"
  /\ UNCHANGED << b, n, f, i, j, k >>

L5 ==
  /\ pc = "L5"
  /\ i' = f[j - k - 1] /\ pc' = "L6"
  /\ UNCHANGED << b, n, f, j, k >>

L6 ==
  /\ pc = "L6"
  /\ IF b[j % n] /= b[(k + i + 1) % n] /\ i /= nil THEN pc' = "L7" ELSE pc' = "L10"
  /\ UNCHANGED << b, n, f, i, j, k >>

L7 ==
  /\ pc = "L7"
  /\ pc' = IF b[j % n] < b[(k + i + 1) % n] THEN "L8" ELSE "L9"
  /\ UNCHANGED << b, n, f, i, j, k >>

L8 ==
  /\ pc = "L8"
  /\ k' = j - i - 1 /\ pc' = "L9"
  /\ UNCHANGED << b, n, f, i, j >>

L9 ==
  /\ pc = "L9"
  /\ i' = f[i] /\ pc' = "L6"
  /\ UNCHANGED << b, n, f, j, k >>

\* The j < 2*n guard of the outer loop does not protect L10 from being
\* reachable; the guard is what keeps this dead end from actually firing.
L10 ==
  /\ pc = "L10"
  /\ pc' = IF b[j % n] /= b[(k + i + 1) % n] /\ i = nil THEN "L11" ELSE "L14"
  /\ UNCHANGED << b, n, f, i, j, k >>

L11 ==
  /\ pc = "L11"
  /\ pc' = IF b[j % n] < b[(k + i + 1) % n] THEN "L12" ELSE "L13"
  /\ UNCHANGED << b, n, f, i, j, k >>

L12 ==
  /\ pc = "L12"
  /\ k' = j /\ pc' = "L13"
  /\ UNCHANGED << b, n, f, i, j >>

L13 ==
  /\ pc = "L13"
  /\ f' = [f EXCEPT ![j - k] = nil] /\ pc' = "LVR"
  /\ UNCHANGED << b, n, i, j, k >>

L14 ==
  /\ pc = "L14"
  /\ f' = [f EXCEPT ![j - k] = i + 1] /\ pc' = "LVR"
  /\ UNCHANGED << b, n, i, j, k >>

LVR ==
  /\ pc = "LVR"
  /\ j' = j + 1 /\ pc' = "L3"
  /\ UNCHANGED << b, n, f, i, k >>

Terminating == pc = "Done" /\ UNCHANGED vars
Next == L3 \/ L5 \/ L6 \/ L7 \/ L8 \/ L9 \/ L10 \/ L11 \/ L12 \/ L13 \/ L14
           \/ LVR \/ Terminating
Spec == Init /\ [][Next]_vars
Termination == <>(pc = "Done")

TypeOK ==
  /\ b \in Corpus /\ n = ZLen(b)
  /\ f \in [0..2*n -> 0..2*n \cup {nil}]
  /\ i \in 0..2*n \cup {nil} /\ j \in 0..2*n \cup {1}
  /\ k \in ZIndices(b) \cup {0}

\* Is this shift the lexicographically-minimal rotation of b?
Least ==
  pc = "Done" =>
    \A other \in Rotations(b) :
      LET r == Rotation(b, k) IN
        /\ r \preceq other.seq
        /\ (r = other.seq => (k <= other.shift))

====