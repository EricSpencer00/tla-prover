---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS CharacterSet, Nat

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
Sentinel == -1

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES
    str,        \* input string, a sequence of characters
    n,          \* length of the input string
    f,          \* failure function array, indexed 0..2*n
    i,          \* pattern-match index (failure function lookup)
    j,          \* outer loop counter, runs from 1 to 2*n
    best,       \* best rotation offset found so far
    pc          \* program counter (label of the current step)

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Chars == CharacterSet

(* Index modulo n, safe for n = 0 (won't be used when n = 0) *)
Mod(i) == IF n = 0 THEN 0 ELSE i % n

(*-----------------------------------------------------------------
  Initial predicate
-----------------------------------------------------------------*)
Init ==
    /\ str \in [0..] -> Chars
    /\ n = Len(str)
    /\ f = [k \in 0..2*n |-> Sentinel]
    /\ i = Sentinel
    /\ j = 1
    /\ best = 0
    /\ pc = "OuterCheck"

(*-----------------------------------------------------------------
  Actions corresponding to the labeled steps
-----------------------------------------------------------------*)
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF j < 2 * n
          THEN /\ pc' = "Lookup"
               /\ UNCHANGED <<str, n, f, i, j, best>>
          ELSE /\ pc' = "Done"
               /\ UNCHANGED <<str, n, f, i, j, best>>

Lookup ==
    /\ pc = "Lookup"
    /\ i' = f[best + j]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<str, n, f, j, best>>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ IF i # Sentinel
          THEN /\ IF str[Mod(j)] # str[Mod(best + i)]
                  THEN /\ pc' = "PostCompare"
                       /\ UNCHANGED <<str, n, f, i, j, best>>
                  ELSE /\ i' = i - 1
                       /\ pc' = "InnerLoop"
                       /\ UNCHANGED <<str, n, f, j, best>>
          ELSE /\ pc' = "PostCompare"
               /\ UNCHANGED <<str, n, f, i, j, best>>

PostCompare ==
    /\ pc = "PostCompare"
    /\ IF str[Mod(j)] # str[Mod(best + i)]
          THEN /\ IF i = Sentinel
                  THEN /\ IF str[Mod(j)] < str[Mod(best + i)]
                          THEN /\ best' = Mod(j - i)
                               /\ UNCHANGED <<str, n, f, i, j>>
                          ELSE UNCHANGED <<best>>
                       /\ f' = [f EXCEPT ![best + j] = Sentinel]
                  ELSE /\ f' = [f EXCEPT ![best + j] = i + 1]
               /\ pc' = "Inc"
          ELSE /\ pc' = "Inc"
               /\ UNCHANGED <<best, f>>
    /\ UNCHANGED <<str, n, i, j>>

Inc ==
    /\ pc = "Inc"
    /\ j' = j + 1
    /\ i' = Sentinel
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<str, n, f, best>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, n, f, i, j, best, pc>>

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, n, f, i, j, best, pc>>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerLoop
    \/ PostCompare
    \/ Inc
    \/ Done
    \/ Stutter

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<str, n, f, i, j, best, pc>>

(*-----------------------------------------------------------------
  Type invariant (ensures variables stay within their domains)
-----------------------------------------------------------------*)
TypeInvariant ==
    /\ str \in [0..] -> Chars
    /\ n = Len(str)
    /\ f \in [0..2*n -> (0..n) \cup {Sentinel}]
    /\ i \in (0..n) \cup {Sentinel}
    /\ j \in 1..(2*n + 1) \cup {0}
    /\ best \in 0..(n - 1) \cup {0}
    /\ pc \in {"OuterCheck", "Lookup", "InnerLoop",
               "PostCompare", "Inc", "Done"}

(*-----------------------------------------------------------------
  Correctness invariant: best points to a lexicographically minimal rotation
-----------------------------------------------------------------*)
Correctness ==
    /\ n = Len(str)
    /\ \A k \in 0..(n-1) :
          LexLeq( Rotation(str, best), Rotation(str, k) )
    /\ \A k \in 0..(n-1) :
          (Rotation(str, best) = Rotation(str, k)) => best <= k

(* Lexicographic less-or-equal between two sequences *)
LexLeq(s, t) ==
    \A m \in 0..(Len(s)-1) :
        ( \A l \in 0..(m-1) : s[l] = t[l] ) => s[m] <= t[m]

(* Rotation of a sequence by offset o (0-indexed) *)
Rotation(s, o) ==
    [i \in 0..(Len(s)-1) |-> s[Mod(o + i)]]

(*-----------------------------------------------------------------
  Theorems (optional, for readability)
-----------------------------------------------------------------*)
THEOREM Spec => []TypeInvariant
THEOREM Spec => []Correctness

====