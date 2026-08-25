---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANT MaxChar

(* A finite version of Nat used to bound character values for model checking. *)
CharacterSet == 0 .. (MaxChar - 1)

ASSUME MaxChar \in Nat \ {0}

VARIABLES s, i, k, best

(* Length of the current input string. *)
n == Len(s)

(* --------------------------------------------------------------------- *)
(* Initialization                                                          *)
(* --------------------------------------------------------------------- *)
Init ==
    /\ s \in Seq(CharacterSet)          \* nondeterministically chosen input
    /\ n > 0
    /\ i = 1                            \* outer loop counter starts at 1
    /\ k = 0                            \* current match length
    /\ best = 0                         \* best rotation offset found so far

(* --------------------------------------------------------------------- *)
(* One step of Booth's linear‑time least‑rotation algorithm               *)
(* --------------------------------------------------------------------- *)
Next ==
    IF i < 2 * n THEN
        LET a == s[(i) % n] IN
        LET b == s[(best + k) % n] IN
        IF a = b THEN
            /\ i' = i + 1
            /\ k' = k + 1
            /\ best' = best
        ELSE IF a < b THEN
            /\ i' = i + 1
            /\ k' = 0
            /\ best' = i - k
        ELSE
            /\ i' = i + 1
            /\ k' = 0
            /\ best' = best
        END
    ELSE
        /\ UNCHANGED << i, k, best >>
    END
    /\ UNCHANGED s

Spec == Init /\ [][Next]_<<s, i, k, best>>

(* --------------------------------------------------------------------- *)
(* Type invariant                                                          *)
(* --------------------------------------------------------------------- *)
TypeInvariant ==
    /\ s \in Seq(CharacterSet)
    /\ n = Len(s)
    /\ n > 0
    /\ i \in 0..2 * n
    /\ k \in 0..n
    /\ best \in 0..n - 1

(* --------------------------------------------------------------------- *)
(* Helper definitions                                                      *)
(* --------------------------------------------------------------------- *)
Rotation(seq, off) ==
    << seq[(off + t) % Len(seq)] : t \in 0..Len(seq) - 1 >>

LexLessOrEqual(a, b) ==
    \/ a = b
    \/ \E m \in 0..Len(a) - 1 :
        /\ a[m] < b[m]
        /\ \A t \in 0..m - 1 : a[t] = b[t]

(* --------------------------------------------------------------------- *)
(* Correctness invariant: best points to the lexicographically minimal   *)
(* rotation of the input string.                                          *)
(* --------------------------------------------------------------------- *)
Correctness ==
    \A j \in 0..n - 1 :
        LexLessOrEqual(Rotation(s, best), Rotation(s, j))

====