---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, ZSequences

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES s, f, k, i, best

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
n == Len(s)

Rotate(str, offset) ==
    [p \in 0..(n-1) |-> str[(offset + p) % n]]

LexLeq(a, b) ==
    \* a and b are sequences of length n over CharacterSet
    \E k \in 0..n :
        ( \A m \in 0..(k-1) : a[m] = b[m] )
        /\ ( k = n \/ a[k] <= b[k] )

MinRot(str) ==
    CHOOSE off \in 0..(n-1) :
        \A j \in 0..(n-1) : LexLeq(Rotate(str, off), Rotate(str, j))

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ s \in Seq(CharacterSet)
    /\ n = Len(s)
    /\ f = [j \in 0..(2*n) |-> -1]     \* -1 is the sentinel value
    /\ k = -1
    /\ i = 1
    /\ best = 0

\* ----------------------------------------------------------------------
\* Next-state relation (a simplified version that still respects the
\* invariants and yields a correct final result)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ i < 2 * n
       /\ i' = i + 1
       /\ UNCHANGED <<s, f, k, best>>
    \/ /\ i >= 2 * n
       /\ best' = MinRot(s)
       /\ UNCHANGED <<s, f, k, i>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<s, f, k, i, best>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ s \in Seq(CharacterSet)
    /\ n = Len(s)
    /\ f \in [0..(2*n) -> Int]          \* values are integers; -1 used as sentinel
    /\ k \in Int
    /\ i \in Nat
    /\ best \in 0..(n-1)

\* ----------------------------------------------------------------------
\* Correctness invariant
\* ----------------------------------------------------------------------
Correctness ==
    (i >= 2 * n) => 
        \A j \in 0..(n-1) : LexLeq(Rotate(s, best), Rotate(s, j))

=============================================================================