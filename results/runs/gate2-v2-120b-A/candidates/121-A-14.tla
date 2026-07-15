---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT CharacterSet \* a finite subset of Nat, supplied by the .cfg
CONSTANT Nat \* just to satisfy the .cfg; not used directly

(*--------------------------------------------------------------------
  Derived values
--------------------------------------------------------------------*)
LenBound == 5 \* an upper bound for the input length; the model
                \* checker can override this via a .cfg file.

Sentinel == -1

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    input,          \* a sequence of characters, indexed from 0
    n,              \* length of the input sequence
    f,              \* failure function: domain = 0..2*n, values = -1..n
    p,              \* current pattern‑match index (or -1)
    i,              \* outer‑loop counter, ranges 1..2*n
    best,           \* best rotation offset found so far, 0..n-1
    pc              \* program counter, one of the labels below

vars == << input, n, f, p, i, best, pc >>

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ input \in Seq(CharacterSet) /\ Len(input) <= LenBound
    /\ n = Len(input)
    /\ f = [j \in 0..2*n |-> Sentinel]
    /\ p = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Idx(j) == j % n          \* index into the circular string
CharAt(j) == input[Idx(j)]

(*--------------------------------------------------------------------
  Actions (one for each labeled step of the algorithm)
--------------------------------------------------------------------*)
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i >= 2*n
          THEN pc' = "Done"
          ELSE pc' = "Lookup"
    /\ UNCHANGED << input, n, f, p, i, best >>

Lookup ==
    /\ pc = "Lookup"
    /\ p' = f[best + i - 1]          \* failure function lookup
    /\ pc' = "InnerLoop"
    /\ UNCHANGED << input, n, f, i, best >>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ IF p # Sentinel
          THEN
            IF CharAt(i) = CharAt(best + p - 1)
                THEN
                    /\ p' = p + 1
                    /\ UNCHANGED << input, n, f, i, best, pc >>
                ELSE
                    /\ pc' = "PostComp"
                    /\ UNCHANGED << input, n, f, i, best, p >>
          ELSE
            /\ pc' = "PostComp"
            /\ UNCHANGED << input, n, f, i, best, p >>

PostComp ==
    /\ pc = "PostComp"
    /\ IF CharAt(i) # CharAt(best + p - 1) /\ p = Sentinel
          THEN
            /\ IF CharAt(i) < CharAt(best + p - 1)
                  THEN best' = Idx(i)
                  ELSE best' = best
            /\ f' = [f EXCEPT ![best + i - 1] = Sentinel]
            /\ pc' = "Inc"
          ELSE
            /\ IF CharAt(i) # CharAt(best + p - 1) /\ CharAt(i) < CharAt(best + p - 1)
                  THEN best' = Idx(i)
                  ELSE best' = best
            /\ f' = [f EXCEPT ![best + i - 1] = p + 1]
            /\ pc' = "Inc"
    /\ UNCHANGED << input, n, p, i >>

Inc ==
    /\ pc = "Inc"
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED << input, n, f, p, best >>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerLoop
    \/ PostComp
    \/ Inc
    \/ Done

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Type invariant (required)
--------------------------------------------------------------------*)
TypeInvariant ==
    /\ input \in Seq(CharacterSet)
    /\ n = Len(input)
    /\ f \in [0..2*n -> Sentinel..n]
    /\ p \in {-1} \cup 0..n
    /\ i \in 1..2*n
    /\ best \in 0..n-1

(*--------------------------------------------------------------------
  Correctness invariant (required)
--------------------------------------------------------------------*)
Correctness ==
    /\ pc = "Done"
    /\ \A k \in 0..n-1 :
          \A j \in 0..n-1 :
            ( ( \A m \in 0..n-1 :
                    CharAt(best + m) = CharAt(k + m) )
              => best <= k )
    /\ best \in 0..n-1

====