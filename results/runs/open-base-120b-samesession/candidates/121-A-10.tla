---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, len, fail, k, i, best, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Sentinel == -1

\* Lexicographic order on rotations
Rot(i, offset) == str[(offset + i) % len]

RotSeq(offset) == [j \in 0..len-1 |-> Rot(j, offset)]

LexLeq(off1, off2) ==
  \E d \in 0..len :
    /\ \A j \in 0..d-1 : Rot(j, off1) = Rot(j, off2)
    /\ (d = len) \/ Rot(d, off1) <= Rot(d, off2)

\* Compute the minimal rotation (used at termination)
BestRotation(s) ==
  LET Offsets == 0..len-1 IN
    CHOOSE off \in Offsets :
      \A off2 \in Offsets : LexLeq(off, off2)

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ len \in Nat
  /\ str \in [0..len-1 -> CharacterSet]
  /\ fail = [j \in 0..2*len-1 |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "OuterCheck"
     /\ i < 2*len
     /\ pc' = "Lookup"
     /\ UNCHANGED <<str, len, fail, k, i, best>>
  \/ /\ pc = "OuterCheck"
     /\ i >= 2*len
     /\ best' = BestRotation(str)
     /\ pc' = "Done"
     /\ UNCHANGED <<str, len, fail, k, i>>
  \/ /\ pc = "Lookup"
     /\ k' = fail[i]
     /\ pc' = "InnerLoop"
     /\ UNCHANGED <<str, len, fail, i, best>>
  \/ /\ pc = "InnerLoop"
     /\ pc' = "PostComp"
     /\ UNCHANGED <<str, len, fail, k, i, best>>
  \/ /\ pc = "PostComp"
     /\ i' = i + 1
     /\ pc' = "OuterCheck"
     /\ UNCHANGED <<str, len, fail, k, best>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<str, len, fail, k, i, best, pc>>

\* ----------------------------------------------------------------------
\* Variable tuple for stuttering
\* ----------------------------------------------------------------------
vars == <<str, len, fail, k, i, best, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ len \in Nat
  /\ str \in [0..len-1 -> CharacterSet]
  /\ fail \in [0..2*len-1 -> Int]
  /\ k \in Int
  /\ i \in Nat
  /\ best \in 0..len-1
  /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "PostComp", "Done"}

\* ----------------------------------------------------------------------
\* Correctness property (lexicographically minimal rotation)
\* ----------------------------------------------------------------------
Correctness ==
  /\ pc = "Done"
  /\ \A off \in 0..len-1 : LexLeq(best, off)

=============================================================================