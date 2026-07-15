---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANT CharacterSet, Nat

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
Sentinel == -1           \* sentinel value for undefined entries

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    s,          \* input string (a sequence of characters)
    n,          \* length of s
    f,          \* failure function array, indexed 0..2*n, values in -1..n
    pi,         \* pattern‑match index, -1..n
    i,          \* outer loop counter, 1..2*n+1
    k,          \* best rotation offset, 0..n-1
    pc          \* program counter (label of the current step)

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Idx(j) == j % n          \* circular index into s

Char(j) == s[Idx(j)]     \* character at circular position j

TypeOk ==
    /\ s \in Seq(CharacterSet)
    /\ n = Len(s)
    /\ n \in Nat
    /\ f \in [0..2*n -> -1..n]
    /\ pi \in -1..n
    /\ i \in 1..2*n+1
    /\ k \in 0..n-1
    /\ pc \in {"OuterCheck", "Lookup", "InnerComp", "UpdateBest",
               "FollowFail", "PostComp", "Inc", "Done"}

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ s \in Seq(CharacterSet)
    /\ n = Len(s)
    /\ f = [j \in 0..2*n |-> Sentinel]
    /\ pi = Sentinel
    /\ i = 1
    /\ k = 0
    /\ pc = "OuterCheck"
    /\ TypeOk

(*--------------------------------------------------------------------
  Actions corresponding to the labeled steps
--------------------------------------------------------------------*)
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i <= 2*n
          THEN /\ pc' = "Lookup"
               /\ UNCHANGED <<s, n, f, pi, i, k>>
          ELSE /\ pc' = "Done"
               /\ UNCHANGED <<s, n, f, pi, i, k>>

Lookup ==
    /\ pc = "Lookup"
    /\ fIdx == i - k
    /\ pi' = f[fIdx]
    /\ pc' = "InnerComp"
    /\ UNCHANGED <<s, n, f, i, k>>

InnerComp ==
    /\ pc = "InnerComp"
    /\ cur = Char(i)
    /\ cand = Char(k + pi + 1)
    /\ IF cur # cand /\ pi # Sentinel
          THEN /\ pc' = "InnerComp"
               /\ pi' = f[pi]
               /\ UNCHANGED <<s, n, f, i, k>>
          ELSE /\ pc' = "PostComp"
               /\ UNCHANGED <<s, n, f, i, k, pi>>

UpdateBest ==
    /\ pc = "UpdateBest"
    /\ k' = i % n
    /\ UNCHANGED <<s, n, f, pi, i>>
    /\ pc' = "FollowFail"

FollowFail ==
    /\ pc = "FollowFail"
    /\ fIdx == i - k
    /\ f' = [f EXCEPT ![fIdx] = pi]
    /\ pi' = pi
    /\ pc' = "Inc"
    /\ UNCHANGED <<s, n, i, k>>

PostComp ==
    /\ pc = "PostComp"
    /\ cur = Char(i)
    /\ cand = Char(k + pi + 1)
    /\ IF cur # cand /\ pi = Sentinel
          THEN
               /\ IF cur < cand
                     THEN /\ k' = i % n
                          /\ pc' = "UpdateBest"
                     ELSE /\ pc' = "Inc"
               /\ UNCHANGED <<s, n, f, pi, i>>
          ELSE
               /\ IF cur < cand
                     THEN /\ k' = i % n
                     ELSE UNCHANGED <<k>>
               /\ fIdx == i - k
               /\ f' = [f EXCEPT ![fIdx] = IF pi = Sentinel THEN 0 ELSE pi + 1]
               /\ pi' = pi
               /\ pc' = "Inc"
               /\ UNCHANGED <<s, n, i>>

Inc ==
    /\ pc = "Inc"
    /\ i' = i + 1
    /\ pi' = Sentinel
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<s, n, f, k>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<s, n, f, pi, i, k, pc>>

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<s, n, f, pi, i, k, pc>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerComp
    \/ UpdateBest
    \/ FollowFail
    \/ PostComp
    \/ Inc
    \/ Done
    \/ Stutter

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<s, n, f, pi, i, k, pc>>

(*--------------------------------------------------------------------
  Type invariant (as required by the .cfg)
--------------------------------------------------------------------*)
TypeInvariant == TypeOk

(*--------------------------------------------------------------------
  Correctness invariant (lexicographically minimal rotation)
--------------------------------------------------------------------*)
LessOrEq(a, b) ==
    \A j \in 0..n-1 :
        IF Char(a + j) # Char(b + j)
           THEN Char(a + j) < Char(b + j)
           ELSE TRUE

Correctness ==
    /\ i = 2*n + 1            \* algorithm has finished
    /\ k \in 0..n-1
    /\ \A r \in 0..n-1 : LessOrEq(k, r)

=============================================================================