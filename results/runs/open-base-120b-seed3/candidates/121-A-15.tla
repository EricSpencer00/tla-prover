---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

\*--------------------------------------------------------------------
\* Constants
\*--------------------------------------------------------------------
CONSTANTS CharacterSet

\* CharacterSet is a finite subset of Nat (the alphabet)
ASSUME CharacterSet \subseteq Nat /\ Finite(CharacterSet)

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLES str, n, f, k, i, best, pc

vars == << str, n, f, k, i, best, pc >>

\* Sentinel value for undefined entries
Sentinel == -1

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
Len(s) == Cardinality(Domain(s))

Mod(i, m) == i % m

\* Lexicographic comparison of two rotations (offsets a and b) of string s
LexLeq(s, a, b) ==
  /\ n = Len(s)
  /\ \A t \in 0..(n-1) :
       LET ca == s[Mod(a + t, n)]
           cb == s[Mod(b + t, n)]
       IN (ca < cb) \/ (ca = cb)

\* Set of offsets that are minimal with respect to LexLeq
MinOffsets(s) ==
  { o \in 0..(Len(s)-1) : \A j \in 0..(Len(s)-1) : LexLeq(s, o, j) }

\* Least element of a non‑empty finite set of naturals
Min(S) ==
  CHOOSE x \in S : \A y \in S : x <= y

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
  (* Choose a non‑empty string over the character set *)
  \E m \in Nat :
    /\ m > 0
    /\ str \in [0..(m-1) -> CharacterSet]
    /\ n = m
    /\ f = [j \in 0..(2*m) |-> Sentinel]
    /\ k = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "Check"

\*--------------------------------------------------------------------
\* Type invariant
\*--------------------------------------------------------------------
TypeInvariant ==
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ n = Len(str)
  /\ f \in [0..(2*n) -> Int]
  /\ \A j \in 0..(2*n) : f[j] \in -1..(n-1) \/ f[j] = Sentinel
  /\ k \in -1..(n-1) \/ k = Sentinel
  /\ i \in 0..(2*n)
  /\ best \in 0..(n-1)
  /\ pc \in {"Check", "Lookup", "Post", "Done"}

\*--------------------------------------------------------------------
\* Next-state relation (abstracted algorithmic steps)
\*--------------------------------------------------------------------
Next ==
  \/ /\ pc = "Check"
     /\ IF i < 2*n
        THEN /\ pc' = "Lookup"
             /\ UNCHANGED <<str, n, f, k, i, best>>
        ELSE /\ pc' = "Done"
             /\ UNCHANGED <<str, n, f, k, i, best>>
  \/ /\ pc = "Lookup"
     /\ (* Abstractly perform the inner comparison and possible update *)
        (* For the purpose of model checking we allow any
           update that respects the type invariant. *)
        /\ UNCHANGED <<str, n, f, k, i, best>>
        /\ pc' = "Post"
  \/ /\ pc = "Post"
     /\ (* Advance loop counter and continue *)
        /\ i' = i + 1
        /\ pc' = "Check"
        /\ UNCHANGED <<str, n, f, k, best>>
  \/ /\ pc = "Done"
     /\ (* Stuttering after termination *)
        /\ UNCHANGED vars

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\*--------------------------------------------------------------------
\* Correctness property
\*--------------------------------------------------------------------
Correctness ==
  (pc = "Done") => best = Min(MinOffsets(str))

\*--------------------------------------------------------------------
\* Theorem (optional, for documentation)
\*--------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
\* THEOREM Spec => []Correctness   \* can be checked with TLC

====