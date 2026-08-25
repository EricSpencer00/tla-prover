---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS CharacterSet

(*--------------------------------------------------------------------
  Sentinel value used for undefined entries in the failure function
---------------------------------------------------------------------*)
Sentinel == -1

VARIABLES str, n, fail, k, i, best, pc

vars == <<str, n, fail, k, i, best, pc>>

(*--------------------------------------------------------------------
  Initialization: nondeterministically choose an input string over the
  given character set and set up all auxiliary variables.
---------------------------------------------------------------------*)
Init ==
    /\ str \in Seq(CharacterSet)
    /\ n = Len(str)
    /\ fail = [j \in 0..2*n |-> Sentinel]
    /\ k = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

(*--------------------------------------------------------------------
  Helper definitions for rotations and lexicographic comparison
---------------------------------------------------------------------*)
RotStr(off) ==
    IF n = 0 THEN <<>>
    ELSE << str[(off + j) % n] : j \in 0..n-1 >>

LessThanSeq(s, t) ==
    \E k \in 0..Len(s) :
        ( \A j \in 0..k-1 : s[j] = t[j] ) /\ (k = Len(s) \/ s[k] < t[k])

RotLexLess(off1, off2) ==
    LessThanSeq(RotStr(off1), RotStr(off2))

(*--------------------------------------------------------------------
  The main loop body: compare the rotation starting at the current
  position with the best one found so far and update if necessary.
---------------------------------------------------------------------*)
Body ==
    /\ pc = "OuterCheck"
    /\ i < 2 * n
    /\ LET cur == i % n IN
         best' = IF RotLexLess(cur, best) THEN cur ELSE best
    /\ i' = i + 1
    /\ UNCHANGED <<str, n, fail, k, pc>>
    /\ best' = best'

(*--------------------------------------------------------------------
  Transition to the terminated state when the outer loop finishes
---------------------------------------------------------------------*)
OuterDone ==
    /\ pc = "OuterCheck"
    /\ i >= 2 * n
    /\ pc' = "Done"
    /\ UNCHANGED <<str, n, fail, k, i, best>>

(*--------------------------------------------------------------------
  Stuttering step after termination
---------------------------------------------------------------------*)
Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Body
    \/ OuterDone
    \/ Done

(*--------------------------------------------------------------------
  Type invariant enforcing the intended domains of all variables
---------------------------------------------------------------------*)
TypeInvariant ==
    /\ str \in Seq(CharacterSet)
    /\ n = Len(str)
    /\ fail \in [0..2*n -> Nat \cup {Sentinel}]
    /\ k \in Nat \cup {Sentinel}
    /\ i \in Nat
    /\ (n = 0 => best = 0) /\ (n > 0 => best \in 0..n-1)
    /\ pc \in {"OuterCheck", "Done"}

(*--------------------------------------------------------------------
  Correctness: upon termination the rotation at 'best' is lexicographically
  minimal among all rotations of the input string.
---------------------------------------------------------------------*)
Correctness ==
    /\ pc = "Done"
    /\ \A off \in (IF n = 0 THEN {} ELSE 0..n-1) :
          ~LessThanSeq(RotStr(off), RotStr(best))

(*--------------------------------------------------------------------
  Specification: initial condition and all possible behaviours
---------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

====