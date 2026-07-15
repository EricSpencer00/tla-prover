---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants (provided by the .cfg)
\* ----------------------------------------------------------------------
CONSTANT CharacterSet
CONSTANT Nat \* the set of natural numbers (for readability)

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
Sentinel == -1           \* value meaning "undefined" in the failure function
MaxLen   == 5            \* upper bound on string length for model checking (set in .cfg)

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    input,          \* the circular string, a sequence of characters
    n,              \* length of the string
    f,              \* failure function, an array indexed 0..2*n
    pi,             \* pattern‑match index (may be Sentinel)
    i,              \* outer loop counter, runs from 1 to 2*n
    best,           \* best rotation offset found so far
    pc              \* program counter, indicates which step is active

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
VariablesExceptPc == << input, n, f, pi, i, best >>

\* The set of possible characters (finite, subset of Nat)
CharSet == CharacterSet

\* Helper for modulo indexing (handles the circular nature)
ModIdx(j) == j % n

\* The rotation of the string starting at offset k
Rotation(k) ==
    IF n = 0 THEN <<>>
    ELSE << input[ ModIdx(k + t) ] : t \in 0..(n-1) >>

\* Lexicographic ordering on sequences of characters
LexLeq(s, t) == 
    \A j \in DOMAIN s : 
        (s[j] # t[j]) => s[j] < t[j]

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ input \in Seq(CharSet)               \* nondeterministic input
    /\ n = Len(input)
    /\ n <= MaxLen
    /\ f = [p \in 0..(2*n) |-> Sentinel]    \* failure function initialized
    /\ pi = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Actions (labeled steps)
\* ----------------------------------------------------------------------
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i >= 2 * n
          THEN /\ pc' = "Done"
               /\ UNCHANGED << input, n, f, pi, i, best >>
          ELSE /\ pc' = "Lookup"
               /\ UNCHANGED << input, n, f, pi, i, best >>

Lookup ==
    /\ pc = "Lookup"
    /\ pi' = f[ i - best ]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED << input, n, f, i, best >>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ IF input[ ModIdx(i) ] = input[ ModIdx(best + pi + 1) ]
          THEN /\ pi' = pi + 1
               /\ pc' = "InnerLoop"
               /\ UNCHANGED << input, n, f, i, best >>
          ELSE IF pi # Sentinel
               THEN /\ pi' = f[ pi ]
                    /\ pc' = "InnerLoop"
                    /\ UNCHANGED << input, n, f, i, best >>
               ELSE /\ pi' = Sentinel
                    /\ pc' = "PostCmp"
                    /\ UNCHANGED << input, n, f, i, best >>

PostCmp ==
    /\ pc = "PostCmp"
    /\ IF input[ ModIdx(i) ] # input[ ModIdx(best + pi + 1) ] /\ pi = Sentinel
          THEN 
               /\ IF input[ ModIdx(i) ] < input[ ModIdx(best + pi + 1) ]
                     THEN best' = i - pi - 1
                     ELSE best' = best
               /\ f' = [f EXCEPT ![i] = IF pi = Sentinel THEN Sentinel ELSE pi + 1]
               /\ pc' = "Increment"
               /\ UNCHANGED << input, n, pi, i >>
          ELSE 
               /\ f' = [f EXCEPT ![i] = IF pi = Sentinel THEN Sentinel ELSE pi + 1]
               /\ best' = best
               /\ pc' = "Increment"
               /\ UNCHANGED << input, n, pi, i >>

Increment ==
    /\ pc = "Increment"
    /\ i' = i + 1
    /\ pi' = Sentinel
    /\ pc' = "OuterCheck"
    /\ UNCHANGED << input, n, f, best >>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED << input, n, f, pi, i, best, pc >>

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED << input, n, f, pi, i, best, pc >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == 
    \/ OuterCheck
    \/ Lookup
    \/ InnerLoop
    \/ PostCmp
    \/ Increment
    \/ Done
    \/ Stutter   \* allows stuttering after termination

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< input, n, f, pi, i, best, pc >>

\* ----------------------------------------------------------------------
\* Type invariant (required)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ input \in Seq(CharSet)
    /\ n = Len(input)
    /\ n <= MaxLen
    /\ f \in [0..(2*n) -> (0..(2*n) \cup {Sentinel})]
    /\ pi \in (0..(2*n)) \cup {Sentinel}
    /\ i \in 1..(2*n)
    /\ best \in 0..(n-1)
    /\ pc \in {"OuterCheck","Lookup","InnerLoop","PostCmp","Increment","Done"}

\* ----------------------------------------------------------------------
\* Correctness invariant (required)
\* ----------------------------------------------------------------------
Correctness ==
    /\ pc = "Done"
    /\ \A k \in 0..(n-1) : 
          LexLeq( Rotation(best), Rotation(k) )
    /\ \A k \in 0..(n-1) :
          ( Rotation(best) = Rotation(k) ) => best <= k

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* THEOREMS (optional, for TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []Correctness
THEOREM Spec => <> (pc = "Done")

====