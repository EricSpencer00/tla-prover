---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

\* -------------------------------------------------
\* Constants
\* -------------------------------------------------
CONSTANTS
    CharacterSet   \* Finite subset of Nat, the alphabet (defined in the .cfg)

\* -------------------------------------------------
\* State variables
\* -------------------------------------------------
VARIABLES
    str,        \* The input string, a function 0..len-1 -> CharacterSet
    len,        \* Length of the input string
    fail,       \* Failure function array, indexed 0..2*len
    k,          \* Pattern‑match index (lookup result)
    i,          \* Outer loop counter, runs from 1 to 2*len
    best,       \* Current best rotation offset
    pc          \* Program counter (label of the next step)

\* -------------------------------------------------
\* Helper definitions
\* -------------------------------------------------
Sentinel == -1

\* Zero‑based circular indexing of the string
CharAt(pos) == 
    IF len = 0 THEN CharacterSet \* degenerate case (never occurs in normal runs)
    ELSE str[(pos % len)]

\* Produce the rotation starting at offset \@ as a sequence 1..len
RotSeq(offset) ==
    [j \in 1..len |-> CharAt(offset + (j-1))]

\* Lexicographic less‑or‑equal on two sequences of the same length
LexLe(s, t) ==
    \A j \in 1..len :
        (\A k \in 1..(j-1) : s[k] = t[k]) => s[j] <= t[j]

\* -------------------------------------------------
\* Initial state
\* -------------------------------------------------
Init ==
    /\ len \in Nat
    /\ len > 0
    /\ str \in [0..len-1 -> CharacterSet]
    /\ fail = [j \in 0..(2*len) |-> Sentinel]
    /\ k = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

\* -------------------------------------------------
\* Actions (one step of the algorithm)
\* -------------------------------------------------
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i < 2*len
       THEN /\ pc' = "Lookup"
            /\ UNCHANGED <<str, len, fail, k, best, i>>
       ELSE /\ pc' = "Done"
            /\ UNCHANGED <<str, len, fail, k, best, i>>

Lookup ==
    /\ pc = "Lookup"
    /\ idx == (i - best) % (2*len + 1)
    /\ k' = fail[idx]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<str, len, fail, best, i>>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ curChar == CharAt(i)
    /\ candChar == CharAt(i - k)
    /\ IF curChar # candChar /\ k # Sentinel
       THEN /\ k' = fail[(i - best - k) % (2*len + 1)]
            /\ pc' = "InnerLoop"
            /\ UNCHANGED <<str, len, fail, best, i>>
       ELSE /\ pc' = "PostComp"
            /\ UNCHANGED <<str, len, fail, best, i, k>>

PostComp ==
    /\ pc = "PostComp"
    /\ curChar == CharAt(i)
    /\ candChar == CharAt(i - k)
    /\ IF curChar # candChar /\ k = Sentinel
       THEN /\ best' = IF curChar < candChar THEN i - k ELSE best
            /\ fail' = [fail EXCEPT ![(i - best) % (2*len + 1)] = 
                        IF curChar = candChar THEN k + 1 ELSE Sentinel]
       ELSE /\ best' = best
            /\ fail' = fail
    /\ pc' = "Inc"
    /\ UNCHANGED k

Inc ==
    /\ pc = "Inc"
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<str, len, fail, k, best>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, len, fail, k, i, best>>

\* Stuttering step to allow the system to stay in the final state
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, len, fail, k, i, best>>

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerLoop
    \/ PostComp
    \/ Inc
    \/ Done
    \/ Stutter

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec ==
    Init /\ [][Next]_<<str, len, fail, k, i, best, pc>>

\* -------------------------------------------------
\* Type invariant
\* -------------------------------------------------
TypeInvariant ==
    /\ len \in Nat
    /\ len > 0
    /\ str \in [0..len-1 -> CharacterSet]
    /\ fail \in [0..(2*len) -> (Nat \cup {Sentinel})]
    /\ k \in (Nat \cup {Sentinel})
    /\ i \in Nat
    /\ i <= 2*len
    /\ best \in 0..(len-1)
    /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "PostComp", "Inc", "Done"}

\* -------------------------------------------------
\* Correctness property (lexicographically minimal rotation)
\* -------------------------------------------------
Correctness ==
    /\ pc = "Done"
    /\ \A shift \in 0..(len-1) :
        LexLe(RotSeq(best), RotSeq(shift))

\* -------------------------------------------------
\* Theorem statements required by the .cfg file
\* -------------------------------------------------
THEOREM SpecTypeInv == Spec => []TypeInvariant
THEOREM SpecCorrect == Spec => []Correctness

====