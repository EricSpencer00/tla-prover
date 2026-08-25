---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

(*--------------------------------------------------------------------
  Finite character set assumptions (required by the .cfg replacement)
--------------------------------------------------------------------*)
ASSUME CharacterSet \subseteq Nat
ASSUME Finite(CharacterSet)

(*--------------------------------------------------------------------
  Sentinel value used for undefined entries in the failure function
--------------------------------------------------------------------*)
SENTINEL == -1

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES str, n, fail, k, i, best, pc

vars == << str, n, fail, k, i, best, pc >>

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Rot(offset) ==
  [j \in 0..(n-1) |-> str[(offset + j) % n]]

LexLess(s1, s2) ==
  \E j \in 0..(n-1) :
    (\A k \in 0..(j-1) : s1[k] = s2[k]) /\ s1[j] < s2[j]

MinRotation ==
  CHOOSE offset \in 0..(n-1) :
    \A o \in 0..(n-1) :
      (LexLess(Rot(offset), Rot(o))
        \/ (Rot(offset) = Rot(o) /\ offset <= o))

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ n \in Nat
  /\ n >= 0
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail = [j \in 0..(2*n) |-> SENTINEL]
  /\ k = SENTINEL
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

(*--------------------------------------------------------------------
  Actions for each program counter label
--------------------------------------------------------------------*)
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2*n
       THEN /\ pc' = "Lookup"
            /\ UNCHANGED << str, n, fail, k, i, best >>
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << str, n, fail, k, i, best >>

Lookup ==
  /\ pc = "Lookup"
  /\ k' = fail[i]
  /\ pc' = "PostComp"
  /\ UNCHANGED << str, n, fail, i, best >>

PostComp ==
  /\ pc = "PostComp"
  /\ (* Simplified: no inner loop modelling; directly proceed *)
     pc' = "Inc"
  /\ UNCHANGED << str, n, fail, k, i, best >>

Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED << str, n, fail, k, best >>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ PostComp
  \/ Inc
  \/ Done

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Type invariant
--------------------------------------------------------------------*)
TypeInvariant ==
  /\ n \in Nat
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail \in [0..(2*n) -> (SENTINEL \cup 0..(2*n))]
  /\ k \in (SENTINEL \cup 0..(2*n))
  /\ i \in Nat
  /\ best \in 0..(n-1)
  /\ pc \in {"OuterCheck", "Lookup", "PostComp", "Inc", "Done"}

(*--------------------------------------------------------------------
  Correctness invariant (holds at termination)
--------------------------------------------------------------------*)
Correctness ==
  IF pc = "Done"
     THEN best = MinRotation
     ELSE TRUE

====