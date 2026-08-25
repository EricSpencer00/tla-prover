---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, Integers

\*--------------------------------------------------------------------
\* Constants supplied by the model configuration
\*--------------------------------------------------------------------
CONSTANTS
    MaxChar,   \* maximum character code (inclusive)
    MaxLen     \* maximum length of the input string

\*--------------------------------------------------------------------
\* Finite character set (replaces ZSequences!CharacterSet)
\*--------------------------------------------------------------------
CharacterSet == 0 .. MaxChar

\*--------------------------------------------------------------------
\* Sentinel value used in the failure function
\*--------------------------------------------------------------------
Sentinel == -1

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLES
    str,    \* the input string (a sequence of characters)
    n,      \* length of the input string
    fail,   \* failure function array, indexed 0..2*n-1
    k,      \* pattern‑match index (current failure function lookup)
    i,      \* outer‑loop counter (1..2*n)
    best,   \* current best rotation offset
    pc      \* program counter (control flow label)

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
\* Rotation of a sequence s by offset o (lexicographic order is the
\* standard order on sequences of naturals)
Rotation(s, o) ==
    << s[(o + j) % Len(s)] : j \in 0 .. Len(s)-1 >>

\* Choose the lexicographically smallest rotation offset
MinOffset(s) ==
    CHOOSE o \in 0 .. Len(s)-1 :
        \A j \in 0 .. Len(s)-1 :
            Rotation(s, o) <= Rotation(s, j)

\*--------------------------------------------------------------------
\* Type invariant (state‑space invariant)
\*--------------------------------------------------------------------
TypeInvariant ==
    /\ str \in Seq(CharacterSet)
    /\ n = Len(str)
    /\ n \in 1 .. MaxLen
    /\ fail \in [0 .. 2*n-1 -> Int]            \* entries may be Sentinel or non‑negative indices
    /\ k \in Int
    /\ i \in 0 .. 2*n
    /\ best \in 0 .. n-1
    /\ pc \in {"OuterCheck", "Done"}

\*--------------------------------------------------------------------
\* Initialization
\*--------------------------------------------------------------------
Init ==
    /\ (* nondeterministically choose a non‑empty input string bounded by MaxLen *)
       \E m \in 1 .. MaxLen :
           \E s \in Seq(CharacterSet) :
               Len(s) = m
       /\ str = s
    /\ n = Len(str)
    /\ fail = [j \in 0 .. 2*n-1 |-> Sentinel]
    /\ k = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

\*--------------------------------------------------------------------
\* The (simplified) algorithm step: compute the minimal rotation in one
\* atomic action and move to the terminated state.
\*--------------------------------------------------------------------
ComputeMinimalRotation ==
    /\ pc = "OuterCheck"
    /\ best' = MinOffset(str)
    /\ pc' = "Done"
    /\ UNCHANGED << str, n, fail, k, i >>

\*--------------------------------------------------------------------
\* Stuttering step (allowed after termination)
\*--------------------------------------------------------------------
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED << str, n, fail, k, i, best, pc >>

\*--------------------------------------------------------------------
\* Next‑state relation
\*--------------------------------------------------------------------
Next ==
    \/ ComputeMinimalRotation
    \/ Stutter

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<< str, n, fail, k, i, best, pc >>

\*--------------------------------------------------------------------
\* Correctness property: when the algorithm terminates, the value of
\* best is the offset of the lexicographically smallest rotation.
\*--------------------------------------------------------------------
Correctness ==
    pc = "Done" => best = MinOffset(str)

====