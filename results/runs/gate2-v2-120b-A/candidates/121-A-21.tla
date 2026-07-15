---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet, Nat

\* ----------------------------------------------------------------------
\* Constants and derived values
\* ----------------------------------------------------------------------
\* The sentinel value is one more than any allowed index.
Sentinel == Nat

\* A state record type (for readability)
SetOfStates == [ 
    str      : Seq(CharacterSet),   \* the input string (zero-indexed)
    len      : Nat,                \* its length
    fail     : [0..2*Nat -> Nat \cup {Sentinel}], \* failure function
    j        : Nat,                \* pattern‑match index
    i        : Nat,                \* outer loop counter
    offset   : Nat,                \* best rotation offset found so far
    pc       : {"OuterLoopCheck", "LookupFail", "InnerComp", 
               "PostComp", "Inc", "Done"}  \* program counter
]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Circular indexing modulo len (len is always > 0)
Circ(s, idx) == 
    IF s = "" THEN "" 
    ELSE s[ (idx % Len(s)) + 1 ]

\* Compare characters at positions p and q (zero‑indexed)
CharAt(s, p) == s[ (p % Len(s)) + 1 ]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES str, len, fail, j, i, offset, pc

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ str \in Seq(CharacterSet)
    /\ len = Len(str)
    /\ len > 0
    /\ fail = [k \in 0..2*Nat |-> Sentinel]
    /\ j = Sentinel
    /\ i = 1
    /\ offset = 0
    /\ pc = "OuterLoopCheck"

\* ----------------------------------------------------------------------
\* Actions (one per labeled step)
\* ----------------------------------------------------------------------
OuterLoopCheck ==
    /\ pc = "OuterLoopCheck"
    /\ IF i < 2 * len THEN 
          pc' = "LookupFail"
       ELSE 
          pc' = "Done"
    /\ UNCHANGED <<str, len, fail, j, i, offset>>

LookupFail ==
    /\ pc = "LookupFail"
    /\ pc' = "InnerComp"
    /\ UNCHANGED <<str, len, fail, j, i, offset>>

InnerComp ==
    /\ pc = "InnerComp"
    /\ LET cur == CharAt(str, i)
           cand == CharAt(str, offset + j + 1)
       IN
       IF cur = cand THEN 
          /\ j' = j + 1
          /\ i' = i + 1
          /\ pc' = "Inc"
          /\ UNCHANGED <<str, len, fail, offset>>
       ELSE 
          IF j # Sentinel THEN
             /\ j' = fail[j]
             /\ pc' = "InnerComp"
          ELSE
             /\ UNCHANGED j
             /\ pc' = "PostComp"
          /\ UNCHANGED <<str, len, fail, i, offset>>

PostComp ==
    /\ pc = "PostComp"
    /\ LET cur == CharAt(str, i)
           cand == CharAt(str, offset + j + 1)
       IN
       /\ IF cur # cand /\ j = Sentinel /\ cur < cand THEN
            offset' = i % len
          ELSE 
            UNCHANGED offset
       /\ IF cur = cand THEN
            fail'[i] = Sentinel
          ELSE
            fail'[i] = IF j = Sentinel THEN Sentinel ELSE j + 1
       /\ i' = i + 1
       /\ j' = Sentinel
       /\ pc' = "Inc"
       /\ UNCHANGED str
       /\ UNCHANGED len

Inc ==
    /\ pc = "Inc"
    /\ i < 2 * len
    /\ i' = i + 1
    /\ pc' = "OuterLoopCheck"
    /\ UNCHANGED <<str, len, fail, j, offset>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, len, fail, j, i, offset, pc>>

\* Stuttering to stay in the terminated state
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, len, fail, j, i, offset, pc>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ OuterLoopCheck
    \/ LookupFail
    \/ InnerComp
    \/ PostComp
    \/ Inc
    \/ Done
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, len, fail, j, i, offset, pc>>

\* ----------------------------------------------------------------------
\* Type invariant (the required INVARIANT)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ str \in Seq(CharacterSet)
    /\ len = Len(str)
    /\ len > 0
    /\ fail \in [0..2*Nat -> Nat \cup {Sentinel}]
    /\ j \in Nat \cup {Sentinel}
    /\ i \in Nat
    /\ offset \in 0..len-1
    /\ pc \in {"OuterLoopCheck", "LookupFail", "InnerComp", 
               "PostComp", "Inc", "Done"}

\* ----------------------------------------------------------------------
\* Correctness invariant (the required INVARIANT)
\* ---------------------------------------------------------------
\* For all possible rotation offsets k, the rotation starting at
\* 'offset' is lexicographically less than or equal to the rotation
\* starting at k.  The rotation is represented as the sequence of
\* characters taken modulo the original length.
\* ----------------------------------------------------------------------
RotationAt(off) == 
    [i \in 1..len |-> CharAt(str, off + i - 1)]

Correctness ==
    \A k \in 0..len-1 :
        LET rOff == RotationAt(offset)
            rK   == RotationAt(k)
        IN  \A m \in 1..len :
                IF rOff[m] # rK[m] THEN rOff[m] < rK[m] ELSE TRUE

\* ----------------------------------------------------------------------
\* Liveness (termination) property
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* The set of invariants required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == TypeInvariant /\ Correctness

=============================================================================